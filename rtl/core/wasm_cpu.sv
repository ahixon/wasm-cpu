// WebAssembly CPU Core
// Main execution unit that orchestrates all components

module wasm_cpu
    import wasm_pkg::*;
#(
    parameter int CODE_SIZE = 65536,   // 64KB code memory
    parameter int STACK_SIZE = STACK_DEPTH,
    parameter int MEM_PAGES = MEMORY_PAGES
)(
    input  logic        clk,
    input  logic        rst_n,

    // Control interface
    input  logic        start,
    input  logic [31:0] entry_func,
    output logic        halted,
    output logic        trapped,
    output trap_t       trap_code,

    // Code memory interface (initialized externally)
    input  logic        code_wr_en,
    input  logic [31:0] code_wr_addr,
    input  logic [7:0]  code_wr_data,

    // Function table interface
    input  logic        func_wr_en,
    input  logic [15:0] func_wr_idx,
    input  func_entry_t func_wr_data,

    // Memory initialization interface
    input  logic        mem_init_en,
    input  logic [31:0] mem_init_pages,
    input  logic [31:0] mem_init_max_pages,  // 0 = no limit beyond MEM_PAGES

    // Memory data initialization interface (for data segments)
    input  logic        mem_data_wr_en,
    input  logic [31:0] mem_data_wr_addr,
    input  logic [7:0]  mem_data_wr_data,

    // Stack initialization interface (for pushing function arguments before start)
    input  logic        stack_init_en,
    input  stack_entry_t stack_init_data,

    // Stack reset interface (for clearing all stacks between invocations)
    input  logic        stack_reset_en,

    // Locals initialization interface (for setting function arguments before start)
    input  logic        local_init_wr_en,
    input  logic [15:0] local_init_wr_base,
    input  logic [7:0]  local_init_wr_idx,
    input  stack_entry_t local_init_wr_data,

    // Global initialization interface
    input  logic        global_init_en,
    input  logic [7:0]  global_init_idx,
    input  global_entry_t global_init_data,

    // Element table initialization interface (for call_indirect)
    input  logic        elem_init_en,
    input  logic [1:0]  elem_init_table_idx,  // Which table (0-3)
    input  logic [15:0] elem_init_idx,
    input  logic [15:0] elem_init_func_idx,  // Function index stored in table

    // Type table initialization interface (for multi-value block types)
    input  logic        type_init_en,
    input  logic [7:0]  type_init_idx,
    input  logic [7:0]  type_init_param_count,
    input  logic [7:0]  type_init_result_count,
    input  logic [31:0] type_init_param_types,
    input  logic [31:0] type_init_result_types,

    // Result output (supports multi-value returns)
    output logic        result_valid,
    output stack_entry_t result_value,          // For single-value backward compatibility
    output logic [7:0]  result_count,           // Number of return values
    output stack_entry_t result_values [0:15],  // Up to 16 return values

    // Debug interface
    output logic [31:0] dbg_pc,
    output exec_state_t dbg_state,
    output logic [15:0] dbg_stack_ptr,
    output logic [31:0] dbg_saved_next_pc,
    output logic [31:0] dbg_decode_next_pc,
    output logic [7:0]  dbg_instr_len,

    // External halt/resume interface (for SoC integration)
    // These have defaults so CPU works standalone without supervisor
    input  logic        ext_halt_i     = 1'b0,    // External halt request
    input  logic        ext_resume_i   = 1'b0,    // Resume from external halt
    input  logic [31:0] ext_resume_pc_i = '0,     // PC to resume at (0 = continue from trap PC)
    input  logic [31:0] ext_resume_val_i = '0,    // Value to push on stack on resume
    output logic        ext_halted_o,             // CPU is externally halted (waiting for resume)

    // Import trap information (valid when trap_code == TRAP_IMPORT)
    output logic [15:0] import_id_o,              // Import function ID (WASI function)
    output logic [31:0] import_arg0_o,            // Import argument 0
    output logic [31:0] import_arg1_o,            // Import argument 1
    output logic [31:0] import_arg2_o,            // Import argument 2
    output logic [31:0] import_arg3_o,            // Import argument 3

    // Debug memory read interface (active when halted)
    input  logic        dbg_mem_rd_en,
    input  logic [31:0] dbg_mem_rd_addr,
    output logic [31:0] dbg_mem_rd_data
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // Program counter
    logic [31:0] pc, next_pc;

    // Execution state machine
    exec_state_t state, next_state;

    // Scanning state for if/else/end
    logic [7:0]  scan_depth;        // Nesting depth during scan
    logic        scan_for_else;     // 1=looking for else/end, 0=just end
    logic        scan_needs_unwind; // 1=branch scan (needs stack unwind), 0=else-skip (no unwind)

    // br_table state
    logic [31:0] br_table_pc;       // Current PC in br_table targets
    logic [31:0] br_table_index;    // Target index to find
    logic [31:0] br_table_count;    // Number of targets
    logic [31:0] br_table_current;  // Current target number being scanned
    logic [7:0]  br_table_depth;    // Branch depth to use
    logic [31:0] scan_br_table_start;  // Start PC for scanning br_table during STATE_SCAN_END
    logic [31:0] scan_br_table_remaining;  // Remaining targets + default to skip

    // Branch stack unwind state
    logic [15:0] branch_target_stack_height;  // Stack height to restore to
    logic [7:0]  branch_target_arity;         // Number of result values to keep (0xFE=save phase, 0xFF=restore phase)
    logic [31:0] branch_target_pc;            // Saved target PC (for func return check)
    stack_entry_t branch_saved_value;         // Saved result value (for arity=1, kept for compatibility)
    logic        branch_pop_pending;          // Pop from br_if that hasn't taken effect yet
    // Multi-value branch support
    stack_entry_t branch_saved_values [0:15]; // Saved result values for multi-value branches
    logic [7:0]  branch_mv_idx;               // Current index during save/restore
    logic [7:0]  branch_mv_arity;             // Actual arity (stored while phases use branch_target_arity)

    // Call state - for copying arguments to locals
    logic [15:0] call_func_idx;       // Index of function being called
    logic [7:0]  call_param_count;    // Number of parameters to copy
    logic [7:0]  call_arg_idx;        // Current argument being written
    logic [15:0] call_new_local_base; // Base address for new function's locals
    logic [15:0] call_peek_offset;    // Peek offset for reading arguments during call
    stack_entry_t call_saved_arg;     // Saved argument from previous peek

    // Result capture state - for multi-value returns
    logic [7:0]  capture_result_idx;    // Current result being captured (0 = TOS = last result)
    logic [7:0]  capture_result_count;  // Total number of results to capture

    // Import trap state - captured when TRAP_IMPORT occurs
    logic [15:0] import_id_q;           // Import function ID
    logic [31:0] import_arg0_q;         // Import arguments
    logic [31:0] import_arg1_q;
    logic [31:0] import_arg2_q;
    logic [31:0] import_arg3_q;

    // Code memory
    logic [7:0] code_mem [0:CODE_SIZE-1];
    logic [7:0] instr_bytes [0:15];
    logic [3:0] bytes_available;

    // Decoded instruction
    logic        decode_valid;
    decoded_instr_t decoded;
    logic [31:0] decode_next_pc;

    // Function table
    func_entry_t func_table [0:MAX_FUNCTIONS-1];

    // Type table - stores full type signature for each type index
    // Used for multi-value block types and call_indirect type checking
    typedef struct packed {
        logic [7:0] param_count;
        logic [7:0] result_count;
        logic [31:0] param_types;   // Up to 8 params, 4 bits each (valtype_t)
        logic [31:0] result_types;  // Up to 8 results, 4 bits each (valtype_t)
    } type_entry_t;
    type_entry_t type_table [0:255];  // Support up to 256 types

    // Element tables (for call_indirect) - stores function indices
    // Entry is 16-bit func index, with 0xFFFF meaning uninitialized
    // Support up to 4 tables with 256 entries each
    logic [15:0] elem_table_0 [0:255];
    logic [15:0] elem_table_1 [0:255];
    logic [15:0] elem_table_2 [0:255];
    logic [15:0] elem_table_3 [0:255];
    logic [15:0] elem_table_size [0:3];  // Size of each table

    // =========================================================================
    // Operand Stack
    // =========================================================================
    logic        stack_push_en;
    stack_entry_t stack_push_data;
    logic        stack_pop_en;
    stack_entry_t stack_pop_data;
    logic [15:0] stack_peek_offset;
    stack_entry_t stack_peek_data;
    logic [15:0] stack_peek_offset2;
    stack_entry_t stack_peek_data2;
    logic        stack_multi_pop_en;
    logic [7:0]  stack_multi_pop_count;
    logic        stack_set_sp_en;
    logic [15:0] stack_set_sp_value;
    logic [15:0] stack_ptr;
    logic        stack_empty, stack_full;
    trap_t       stack_trap;

    // Combined push for internal operations and external initialization
    logic        stack_push_combined;
    stack_entry_t stack_push_data_combined;

    // Combined set_sp for internal operations and external reset
    logic        stack_set_sp_combined;
    logic [15:0] stack_set_sp_value_combined;

    // Allow external stack init when idle, halted, or trapped
    assign stack_push_combined = stack_push_en | (stack_init_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP));
    assign stack_push_data_combined = (stack_init_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP))
                                      ? stack_init_data : stack_push_data;

    // Allow external stack reset when idle, halted, or trapped
    assign stack_set_sp_combined = stack_set_sp_en | (stack_reset_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP));
    assign stack_set_sp_value_combined = (stack_reset_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP))
                                         ? 16'h0 : stack_set_sp_value;

    wasm_stack #(.DEPTH(STACK_SIZE)) operand_stack (
        .clk(clk),
        .rst_n(rst_n),
        .push_en(stack_push_combined),
        .push_data(stack_push_data_combined),
        .pop_en(stack_pop_en),
        .pop_data(stack_pop_data),
        .peek_offset(stack_peek_offset),
        .peek_data(stack_peek_data),
        .peek_offset2(stack_peek_offset2),
        .peek_data2(stack_peek_data2),
        .multi_pop_en(stack_multi_pop_en),
        .multi_pop_count(stack_multi_pop_count),
        .set_sp_en(stack_set_sp_combined),
        .set_sp_value(stack_set_sp_value_combined),
        .stack_ptr(stack_ptr),
        .empty(stack_empty),
        .full(stack_full),
        .trap(stack_trap)
    );

    // =========================================================================
    // Label Stack
    // =========================================================================
    logic        label_push_en;
    label_entry_t label_push_data;
    logic        label_pop_en;
    label_entry_t label_pop_data;
    logic [7:0]  label_branch_depth_comb; // Combinational depth for target lookup
    label_entry_t label_branch_target;
    logic        label_branch_pop_en;
    logic        label_set_sp_en;
    logic [7:0]  label_set_sp_value;
    logic [7:0]  label_stack_ptr;
    logic        label_empty, label_full;

    // Combinational branch depth selection
    always_comb begin
        // Default to saved decoded immediate for br/br_if
        // During STATE_BR_TABLE and subsequent states, use br_table_depth
        if (state == STATE_BR_TABLE || (saved_decoded.opcode == OP_BR_TABLE &&
            (state == STATE_SCAN_END || state == STATE_BR_UNWIND)))
            label_branch_depth_comb = br_table_depth;
        else
            label_branch_depth_comb = saved_decoded.immediate[7:0];
    end

    // Combinational logic for stack peek offsets
    // Must be in always_comb so peek_data is valid when read in always_ff
    always_comb begin
        // Default offsets for most operations
        if (state == STATE_CALL) begin
            stack_peek_offset = call_peek_offset;  // Use call-specific offset
            stack_peek_offset2 = 16'd0;
        end else if (state == STATE_CAPTURE_RESULTS) begin
            // Capture results: peek at stack starting from TOS (offset 0)
            // capture_result_idx is the current index being captured
            stack_peek_offset = {8'b0, capture_result_idx};
            stack_peek_offset2 = 16'd0;
        end else if (state == STATE_BR_UNWIND && branch_target_arity == 8'hFE) begin
            // Multi-value branch save phase: peek at values from TOS down
            // If pop_pending (from br_if), the condition is at TOS so skip it (add 1)
            // branch_mv_idx=0 -> TOS (offset 0 or 1), branch_mv_idx=1 -> TOS-1 (offset 1 or 2), etc.
            stack_peek_offset = branch_pop_pending ? ({8'b0, branch_mv_idx} + 16'd1) : {8'b0, branch_mv_idx};
            stack_peek_offset2 = 16'd0;
        end else begin
            stack_peek_offset = 16'd1;   // TOS-1
            stack_peek_offset2 = 16'd2;  // TOS-2
        end
    end

    // Combined set_sp for label stack: internal operations and external reset
    logic        label_set_sp_combined;
    logic [7:0]  label_set_sp_value_combined;

    assign label_set_sp_combined = label_set_sp_en | (stack_reset_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP));
    assign label_set_sp_value_combined = (stack_reset_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP))
                                         ? 8'h0 : label_set_sp_value;

    wasm_label_stack label_stack (
        .clk(clk),
        .rst_n(rst_n),
        .push_en(label_push_en),
        .push_data(label_push_data),
        .pop_en(label_pop_en),
        .pop_data(label_pop_data),
        .branch_depth(label_branch_depth_comb),  // Use combinational depth for lookup
        .branch_target(label_branch_target),
        .branch_pop_en(label_branch_pop_en),
        .set_sp_en(label_set_sp_combined),
        .set_sp_value(label_set_sp_value_combined),
        .stack_ptr(label_stack_ptr),
        .empty(label_empty),
        .full(label_full)
    );

    // =========================================================================
    // Call Stack
    // =========================================================================
    logic        frame_push_en;
    frame_entry_t frame_push_data;
    logic        frame_pop_en;
    frame_entry_t frame_pop_data;
    frame_entry_t current_frame;
    logic [7:0]  frame_stack_ptr;
    logic        frame_empty, frame_full;
    trap_t       frame_trap;

    // Combined set_sp for frame stack: external reset
    logic        frame_set_sp_combined;
    logic [7:0]  frame_set_sp_value_combined;

    assign frame_set_sp_combined = (stack_reset_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP));
    assign frame_set_sp_value_combined = 8'h0;

    wasm_call_stack call_stack (
        .clk(clk),
        .rst_n(rst_n),
        .push_en(frame_push_en),
        .push_data(frame_push_data),
        .pop_en(frame_pop_en),
        .pop_data(frame_pop_data),
        .set_sp_en(frame_set_sp_combined),
        .set_sp_value(frame_set_sp_value_combined),
        .current_frame(current_frame),
        .stack_ptr(frame_stack_ptr),
        .empty(frame_empty),
        .full(frame_full),
        .trap(frame_trap)
    );

    // =========================================================================
    // Linear Memory
    // =========================================================================
    logic        mem_rd_en;
    logic [31:0] mem_rd_addr;
    mem_op_t     mem_rd_op;
    logic [63:0] mem_rd_data;
    logic        mem_rd_valid;
    logic        mem_wr_en;
    logic [31:0] mem_wr_addr;
    mem_op_t     mem_wr_op;
    logic [63:0] mem_wr_data;
    logic        mem_wr_valid;
    logic        mem_grow_en;
    logic [31:0] mem_grow_pages;
    logic [31:0] mem_current_pages;
    logic [31:0] mem_grow_result;
    trap_t       mem_trap;

    wasm_memory #(.MAX_PAGES(MEM_PAGES)) linear_memory (
        .clk(clk),
        .rst_n(rst_n),
        .init_en(mem_init_en),
        .init_pages(mem_init_pages),
        .init_max_pages(mem_init_max_pages),
        .data_wr_en(mem_data_wr_en),
        .data_wr_addr(mem_data_wr_addr),
        .data_wr_data(mem_data_wr_data),
        .rd_en(mem_rd_en),
        .rd_addr(mem_rd_addr),
        .rd_op(mem_rd_op),
        .rd_data(mem_rd_data),
        .rd_valid(mem_rd_valid),
        .wr_en(mem_wr_en),
        .wr_addr(mem_wr_addr),
        .wr_op(mem_wr_op),
        .wr_data(mem_wr_data),
        .wr_valid(mem_wr_valid),
        .grow_en(mem_grow_en),
        .grow_pages(mem_grow_pages),
        .current_pages(mem_current_pages),
        .grow_result(mem_grow_result),
        .trap(mem_trap),
        .dbg_rd_en(dbg_mem_rd_en),
        .dbg_rd_addr(dbg_mem_rd_addr),
        .dbg_rd_data(dbg_mem_rd_data)
    );

    // =========================================================================
    // Local Variables
    // =========================================================================
    logic        local_rd_en;
    logic [15:0] local_base_idx;
    logic [7:0]  local_idx;
    stack_entry_t local_rd_data;
    logic        local_rd_valid;
    logic        local_wr_en;
    logic [15:0] local_wr_base_idx;
    logic [7:0]  local_wr_idx;
    stack_entry_t local_wr_data;
    logic        local_wr_valid;

    valtype_t local_init_types [0:31];
    assign local_init_types = '{default: TYPE_I32};

    // Combined write for internal operations and external initialization
    logic        local_wr_combined;
    logic [15:0] local_wr_base_combined;
    logic [7:0]  local_wr_idx_combined;
    stack_entry_t local_wr_data_combined;

    assign local_wr_combined = local_wr_en | (local_init_wr_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP));
    assign local_wr_base_combined = (local_init_wr_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP))
                                    ? local_init_wr_base : local_wr_base_idx;
    assign local_wr_idx_combined = (local_init_wr_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP))
                                   ? local_init_wr_idx : local_wr_idx;
    assign local_wr_data_combined = (local_init_wr_en && (state == STATE_IDLE || state == STATE_HALT || state == STATE_TRAP))
                                    ? local_init_wr_data : local_wr_data;

    wasm_locals locals_inst (
        .clk(clk),
        .rst_n(rst_n),
        .rd_en(local_rd_en),
        .base_idx(local_base_idx),
        .local_idx(local_idx),
        .rd_data(local_rd_data),
        .rd_valid(local_rd_valid),
        .wr_en(local_wr_combined),
        .wr_base_idx(local_wr_base_combined),
        .wr_local_idx(local_wr_idx_combined),
        .wr_data(local_wr_data_combined),
        .wr_valid(local_wr_valid),
        .init_en(1'b0),
        .init_base(16'h0),
        .init_count(8'h0),
        .init_types(local_init_types),
        .next_free_base()
    );

    // =========================================================================
    // Global Variables
    // =========================================================================
    logic        global_rd_en;
    logic [7:0]  global_rd_idx;
    stack_entry_t global_rd_data;
    logic        global_rd_valid;
    logic        global_wr_en;
    logic [7:0]  global_wr_idx;
    stack_entry_t global_wr_data;
    logic        global_wr_valid;
    logic        global_wr_error;

    wasm_globals globals_inst (
        .clk(clk),
        .rst_n(rst_n),
        .rd_en(global_rd_en),
        .rd_idx(global_rd_idx),
        .rd_data(global_rd_data),
        .rd_valid(global_rd_valid),
        .wr_en(global_wr_en),
        .wr_idx(global_wr_idx),
        .wr_data(global_wr_data),
        .wr_valid(global_wr_valid),
        .wr_error(global_wr_error),
        .init_en(global_init_en),
        .init_idx(global_init_idx),
        .init_data(global_init_data),
        .num_globals()
    );

    // =========================================================================
    // ALU Units
    // =========================================================================
    logic        alu_i32_valid_in;
    alu_op_t     alu_i32_op;
    logic [31:0] alu_i32_a, alu_i32_b;
    logic        alu_i32_valid_out;
    logic [31:0] alu_i32_result;
    trap_t       alu_i32_trap;

    wasm_alu_i32 alu_i32 (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(alu_i32_valid_in),
        .op(alu_i32_op),
        .operand_a(alu_i32_a),
        .operand_b(alu_i32_b),
        .valid_out(alu_i32_valid_out),
        .result(alu_i32_result),
        .trap(alu_i32_trap)
    );

    logic        alu_i64_valid_in;
    alu_op_t     alu_i64_op;
    logic [63:0] alu_i64_a, alu_i64_b;
    logic        alu_i64_valid_out;
    logic [63:0] alu_i64_result;
    trap_t       alu_i64_trap;

    wasm_alu_i64 alu_i64 (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(alu_i64_valid_in),
        .op(alu_i64_op),
        .operand_a(alu_i64_a),
        .operand_b(alu_i64_b),
        .valid_out(alu_i64_valid_out),
        .result(alu_i64_result),
        .trap(alu_i64_trap)
    );

    // =========================================================================
    // FPU Units
    // =========================================================================
    logic        fpu_f32_valid_in;
    fpu_op_t     fpu_f32_op;
    logic [31:0] fpu_f32_a, fpu_f32_b;
    logic        fpu_f32_valid_out;
    logic [31:0] fpu_f32_result;
    trap_t       fpu_f32_trap;

    wasm_fpu_f32 fpu_f32 (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(fpu_f32_valid_in),
        .op(fpu_f32_op),
        .operand_a(fpu_f32_a),
        .operand_b(fpu_f32_b),
        .valid_out(fpu_f32_valid_out),
        .result(fpu_f32_result),
        .trap(fpu_f32_trap)
    );

    logic        fpu_f64_valid_in;
    fpu_op_t     fpu_f64_op;
    logic [63:0] fpu_f64_a, fpu_f64_b;
    logic        fpu_f64_valid_out;
    logic [63:0] fpu_f64_result;
    trap_t       fpu_f64_trap;

    wasm_fpu_f64 fpu_f64 (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(fpu_f64_valid_in),
        .op(fpu_f64_op),
        .operand_a(fpu_f64_a),
        .operand_b(fpu_f64_b),
        .valid_out(fpu_f64_valid_out),
        .result(fpu_f64_result),
        .trap(fpu_f64_trap)
    );

    // =========================================================================
    // Conversion Unit
    // =========================================================================
    logic        conv_valid_in;
    opcode_t     conv_op;
    logic [7:0]  conv_sub_op;     // For extended opcodes
    logic [63:0] conv_operand;
    logic        conv_valid_out;
    logic [63:0] conv_result;
    trap_t       conv_trap;

    wasm_conv converter (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(conv_valid_in),
        .op(conv_op),
        .sub_op(conv_sub_op),
        .operand(conv_operand),
        .valid_out(conv_valid_out),
        .result(conv_result),
        .trap(conv_trap)
    );

    // =========================================================================
    // Decoder
    // =========================================================================
    wasm_decoder decoder (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(state == STATE_DECODE),
        .pc(pc),
        .instr_bytes(instr_bytes),
        .bytes_available(bytes_available),
        .valid_out(decode_valid),
        .decoded(decoded),
        .next_pc(decode_next_pc)
    );

    // =========================================================================
    // Code Memory Interface
    // =========================================================================
    always_ff @(posedge clk) begin
        if (code_wr_en) begin
            code_mem[code_wr_addr] <= code_wr_data;
        end
    end

    // Fetch instruction bytes
    always_comb begin
        bytes_available = 4'd15;
        for (int i = 0; i < 16; i++) begin
            if (pc + i < CODE_SIZE) begin
                instr_bytes[i] = code_mem[pc + i];
            end else begin
                instr_bytes[i] = 8'h00;
            end
        end
    end

    // =========================================================================
    // Function Table Interface
    // =========================================================================
    always_ff @(posedge clk) begin
        if (func_wr_en) begin
            func_table[func_wr_idx] <= func_wr_data;
        end
    end

    // =========================================================================
    // Element Table Interface (for call_indirect)
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize all table sizes to 0
            for (int t = 0; t < 4; t++) begin
                elem_table_size[t] <= 16'h0;
            end
            // Initialize all entries to 0xFFFF (uninitialized marker)
            for (int i = 0; i < 256; i++) begin
                elem_table_0[i] <= 16'hFFFF;
                elem_table_1[i] <= 16'hFFFF;
                elem_table_2[i] <= 16'hFFFF;
                elem_table_3[i] <= 16'hFFFF;
            end
        end else if (elem_init_en) begin
            // Write to the appropriate table based on table index
            case (elem_init_table_idx)
                2'd0: elem_table_0[elem_init_idx[7:0]] <= elem_init_func_idx;
                2'd1: elem_table_1[elem_init_idx[7:0]] <= elem_init_func_idx;
                2'd2: elem_table_2[elem_init_idx[7:0]] <= elem_init_func_idx;
                2'd3: elem_table_3[elem_init_idx[7:0]] <= elem_init_func_idx;
            endcase
            // Track the highest index + 1 as size for this table
            if (elem_init_idx >= elem_table_size[elem_init_table_idx]) begin
                elem_table_size[elem_init_table_idx] <= elem_init_idx + 16'h1;
            end
        end
    end

    // =========================================================================
    // Type Table Interface (for multi-value block types)
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize all entries to single-value types by default
            for (int i = 0; i < 256; i++) begin
                type_table[i].param_count <= 8'h0;
                type_table[i].result_count <= 8'h1;  // Default to 1 result
            end
        end else if (type_init_en) begin
            type_table[type_init_idx].param_count <= type_init_param_count;
            type_table[type_init_idx].result_count <= type_init_result_count;
            type_table[type_init_idx].param_types <= type_init_param_types;
            type_table[type_init_idx].result_types <= type_init_result_types;
        end
    end

    // =========================================================================
    // Debug Outputs
    // =========================================================================
    assign dbg_pc = pc;
    assign dbg_state = state;
    assign dbg_stack_ptr = stack_ptr;
    assign dbg_saved_next_pc = saved_next_pc;
    assign dbg_decode_next_pc = decode_next_pc;
    assign dbg_instr_len = decoded.instr_length;

    // =========================================================================
    // Execution State Machine
    // =========================================================================

    // Intermediate values for execution
    stack_entry_t operand_a, operand_b, operand_c;
    logic [31:0] effective_addr;
    logic [32:0] effective_addr_full;  // 33-bit to detect overflow
    logic        effective_addr_overflow;
    logic [63:0] exec_result;
    valtype_t    exec_result_type;
    logic        exec_trap_flag;
    trap_t       exec_trap;

    // Saved decoded instruction and next PC
    decoded_instr_t saved_decoded;
    logic [31:0] saved_next_pc;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= STATE_IDLE;
            pc <= 32'h0;
            halted <= 1'b0;
            trapped <= 1'b0;
            trap_code <= TRAP_NONE;
            result_valid <= 1'b0;
            result_value <= '0;
            result_count <= 8'h0;
            for (int i = 0; i < 8; i++) result_values[i] <= '0;
            capture_result_idx <= 8'h0;
            capture_result_count <= 8'h0;
            saved_decoded <= '0;
            saved_next_pc <= 32'h0;
            exec_result <= 64'h0;
            exec_result_type <= TYPE_I32;
            scan_depth <= 8'h0;
            scan_for_else <= 1'b0;
            scan_needs_unwind <= 1'b0;
            br_table_depth <= 8'h0;
            br_table_pc <= 32'h0;
            br_table_index <= 32'h0;
            br_table_count <= 32'h0;
            br_table_current <= 32'h0;
            branch_target_stack_height <= 16'h0;
            branch_target_arity <= 8'h0;
            branch_target_pc <= 32'h0;
            branch_saved_value <= '0;
            branch_pop_pending <= 1'b0;
            branch_mv_idx <= 8'h0;
            branch_mv_arity <= 8'h0;
            // Import trap state
            import_id_q <= 16'h0;
            import_arg0_q <= 32'h0;
            import_arg1_q <= 32'h0;
            import_arg2_q <= 32'h0;
            import_arg3_q <= 32'h0;
        end else begin
            // Default assignments
            stack_push_en <= 1'b0;
            stack_pop_en <= 1'b0;
            stack_multi_pop_en <= 1'b0;
            stack_set_sp_en <= 1'b0;
            label_push_en <= 1'b0;
            label_pop_en <= 1'b0;
            label_branch_pop_en <= 1'b0;
            label_set_sp_en <= 1'b0;
            frame_push_en <= 1'b0;
            frame_pop_en <= 1'b0;
            mem_rd_en <= 1'b0;
            mem_wr_en <= 1'b0;
            mem_grow_en <= 1'b0;
            local_rd_en <= 1'b0;
            local_wr_en <= 1'b0;
            global_rd_en <= 1'b0;
            global_wr_en <= 1'b0;
            alu_i32_valid_in <= 1'b0;
            alu_i64_valid_in <= 1'b0;
            fpu_f32_valid_in <= 1'b0;
            fpu_f64_valid_in <= 1'b0;
            conv_valid_in <= 1'b0;
            conv_sub_op <= 8'h0;
            result_valid <= 1'b0;

            case (state)
                STATE_IDLE: begin
                    if (start) begin
                        // Start execution at entry function
                        pc <= func_table[entry_func].code_offset;
                        state <= STATE_FETCH;
                        halted <= 1'b0;
                        trapped <= 1'b0;

                        // Push initial frame for entry function
                        // Use current stack_ptr as local_base - args are already on stack
                        frame_push_en <= 1'b1;
                        frame_push_data.return_pc <= 32'hFFFFFFFF;  // Special: no return
                        frame_push_data.func_idx <= entry_func[15:0];
                        frame_push_data.local_base <= stack_ptr;
                        frame_push_data.stack_height <= stack_ptr;
                        frame_push_data.label_height <= 8'h0;
                        frame_push_data.arity <= func_table[entry_func].result_count;
                    end
                end

                STATE_FETCH: begin
                    // Move to decode immediately (instruction bytes are ready combinationally)
                    state <= STATE_DECODE;
                end

                STATE_DECODE: begin
                    if (decode_valid) begin
                        saved_decoded <= decoded;
                        saved_next_pc <= decode_next_pc;
                        state <= STATE_EXECUTE;
                    end
                end

                STATE_EXECUTE: begin
                    // Read stack values for operations
                    // peek offsets are set combinationally in always_comb block above
                    // Read values
                    operand_a = stack_pop_data;  // TOS
                    operand_b = stack_peek_data;  // TOS-1 (offset 1)
                    operand_c = stack_peek_data2; // TOS-2 (offset 2)

                    case (saved_decoded.opcode)
                        // ==== Control Instructions ====
                        OP_UNREACHABLE: begin
                            trapped <= 1'b1;
                            trap_code <= TRAP_UNREACHABLE;
                            state <= STATE_TRAP;
                        end

                        OP_NOP: begin
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_BLOCK: begin
                            // Push label for block continuation
                            label_push_en <= 1'b1;
                            label_push_data.target_pc <= 32'h0;  // Will be set when we find END
                            label_push_data.stack_height <= stack_ptr;
                            // Determine block arity from block type:
                            // 0xFFFFFFFF (from 0x40) = void (0 results)
                            // 0x7C-0x7F = single value type (1 result)
                            // Otherwise = type index, look up in type_table
                            if (saved_decoded.immediate == 64'hFFFFFFFF)
                                label_push_data.arity <= 8'h0;
                            else if (saved_decoded.immediate >= 64'h7C && saved_decoded.immediate <= 64'h7F)
                                label_push_data.arity <= 8'h1;
                            else
                                label_push_data.arity <= type_table[saved_decoded.immediate[7:0]].result_count;
                            label_push_data.is_loop <= 1'b0;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_LOOP: begin
                            // Push label for loop start
                            label_push_en <= 1'b1;
                            label_push_data.target_pc <= saved_next_pc;  // Loop branches go to start
                            label_push_data.stack_height <= stack_ptr;
                            label_push_data.arity <= 8'h0;  // Loop takes no params from stack
                            label_push_data.is_loop <= 1'b1;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_IF: begin
                            // Pop condition
                            stack_pop_en <= 1'b1;
                            if (operand_a.value[31:0] != 32'h0) begin
                                // Condition true (non-zero) - enter if block
                                label_push_en <= 1'b1;
                                label_push_data.target_pc <= 32'h0;
                                label_push_data.stack_height <= stack_ptr - 1;
                                // Determine if block arity from block type
                                if (saved_decoded.immediate == 64'hFFFFFFFF)
                                    label_push_data.arity <= 8'h0;
                                else if (saved_decoded.immediate >= 64'h7C && saved_decoded.immediate <= 64'h7F)
                                    label_push_data.arity <= 8'h1;
                                else
                                    label_push_data.arity <= type_table[saved_decoded.immediate[7:0]].result_count;
                                label_push_data.is_loop <= 1'b0;
                                pc <= saved_next_pc;
                                state <= STATE_FETCH;
                            end else begin
                                // Condition false - skip to else/end
                                scan_depth <= 8'h0;
                                scan_for_else <= 1'b1;
                                pc <= saved_next_pc;
                                state <= STATE_SCAN_ELSE;
                            end
                        end

                        OP_ELSE: begin
                            // After then-block, skip to end of if-else
                            label_pop_en <= 1'b1;  // Pop the if label
                            scan_depth <= 8'h0;
                            scan_for_else <= 1'b0;
                            scan_needs_unwind <= 1'b0;  // Else-skip doesn't need unwinding
                            pc <= saved_next_pc;
                            state <= STATE_SCAN_END;
                        end

                        OP_END: begin
                            // Check if this is function end (no labels pushed by this function)
                            if (label_empty || label_stack_ptr == current_frame.label_height) begin
                                // Function return - don't pop any labels (none belong to this function)
                                if (current_frame.return_pc == 32'hFFFFFFFF) begin
                                    // Entry function return - capture results then halt
                                    capture_result_count <= current_frame.arity;
                                    capture_result_idx <= 8'h0;
                                    frame_pop_en <= 1'b1;  // Pop entry frame
                                    state <= STATE_CAPTURE_RESULTS;
                                end else begin
                                    frame_pop_en <= 1'b1;
                                    pc <= current_frame.return_pc;
                                    state <= STATE_FETCH;
                                end
                            end else begin
                                // Block end - pop the label
                                label_pop_en <= 1'b1;
                                pc <= saved_next_pc;
                                state <= STATE_FETCH;
                            end
                        end

                        OP_BR: begin
                            // Unconditional branch
                            // Check if branch targets function level (implicit function block)
                            // func_label_count = labels pushed in this function
                            logic [7:0] br_func_label_count;
                            logic br_is_func_return;
                            br_func_label_count = label_stack_ptr - current_frame.label_height;
                            br_is_func_return = (saved_decoded.immediate[7:0] >= br_func_label_count);
                            if (br_is_func_return) begin
                                // Branch to function block = return
                                // Restore label stack to frame's label height
                                label_set_sp_en <= 1'b1;
                                label_set_sp_value <= current_frame.label_height;
                                // Save target info for stack unwinding
                                branch_target_stack_height <= current_frame.stack_height;
                                branch_target_arity <= current_frame.arity;
                                branch_target_pc <= 32'hFFFFFFFF;  // Mark as function return
                                // Save branch value (TOS = operand_a) for STATE_BR_UNWIND
                                branch_saved_value <= operand_a;
                                state <= STATE_BR_UNWIND;
                            end else begin
                                // Save target info for stack unwinding
                                branch_target_stack_height <= label_branch_target.stack_height;
                                branch_target_arity <= label_branch_target.arity;
                                branch_target_pc <= label_branch_target.target_pc;
                                if (label_branch_target.is_loop) begin
                                    // Loop: pop intermediate labels but keep loop's label
                                    // Pop only branch_depth labels (not branch_depth + 1)
                                    if (saved_decoded.immediate[7:0] > 0) begin
                                        label_set_sp_en <= 1'b1;
                                        label_set_sp_value <= label_stack_ptr - saved_decoded.immediate[7:0];
                                    end
                                    pc <= label_branch_target.target_pc;
                                    state <= STATE_FETCH;
                                end else begin
                                    // Block: pop labels including target block
                                    label_branch_pop_en <= 1'b1;
                                    // Block - scan forward to find END, then unwind stack
                                    scan_depth <= saved_decoded.immediate[7:0];
                                    scan_for_else <= 1'b0;
                                    scan_needs_unwind <= 1'b1;  // Branch needs stack unwinding
                                    pc <= saved_next_pc;
                                    state <= STATE_SCAN_END;
                                end
                            end
                        end

                        OP_BR_IF: begin
                            stack_pop_en <= 1'b1;
                            if (operand_a.value[31:0] != 32'h0) begin
                                // Take branch (condition is non-zero)
                                // Check if branch targets function level
                                logic [7:0] brif_func_label_count;
                                logic brif_is_func_return;
                                brif_func_label_count = label_stack_ptr - current_frame.label_height;
                                brif_is_func_return = (saved_decoded.immediate[7:0] >= brif_func_label_count);

                                if (brif_is_func_return) begin
                                    // Branch to function block = return
                                    label_set_sp_en <= 1'b1;
                                    label_set_sp_value <= current_frame.label_height;
                                    branch_target_stack_height <= current_frame.stack_height;
                                    branch_target_arity <= current_frame.arity;
                                    branch_target_pc <= 32'hFFFFFFFF;
                                    // Save branch value now (operand_b = TOS-1) since the condition pop
                                    // won't take effect until next cycle
                                    branch_saved_value <= operand_b;
                                    // Mark that a pop is pending so STATE_BR_UNWIND adjusts stack_ptr
                                    branch_pop_pending <= 1'b1;
                                    state <= STATE_BR_UNWIND;
                                end else begin
                                    branch_target_stack_height <= label_branch_target.stack_height;
                                    branch_target_arity <= label_branch_target.arity;
                                    branch_target_pc <= label_branch_target.target_pc;
                                    if (label_branch_target.is_loop) begin
                                        // Loop: pop intermediate labels but keep loop's label
                                        if (saved_decoded.immediate[7:0] > 0) begin
                                            label_set_sp_en <= 1'b1;
                                            label_set_sp_value <= label_stack_ptr - saved_decoded.immediate[7:0];
                                        end
                                        pc <= label_branch_target.target_pc;
                                        state <= STATE_FETCH;
                                    end else begin
                                        // Block: pop labels including target block
                                        label_branch_pop_en <= 1'b1;
                                        // Block - scan forward to find END, then unwind stack
                                        scan_depth <= saved_decoded.immediate[7:0];
                                        scan_for_else <= 1'b0;
                                        scan_needs_unwind <= 1'b1;
                                        pc <= saved_next_pc;
                                        state <= STATE_SCAN_END;
                                    end
                                end
                            end else begin
                                pc <= saved_next_pc;
                                state <= STATE_FETCH;
                            end
                        end

                        OP_BR_TABLE: begin
                            // Branch table: pop index, select target based on index
                            // immediate = count of targets
                            // immediate2 = offset to first target (bytes after opcode for count)
                            stack_pop_en <= 1'b1;
                            br_table_index <= operand_a.value[31:0];
                            br_table_count <= saved_decoded.immediate[31:0];
                            br_table_pc <= pc + 1 + saved_decoded.immediate2;  // Start of targets
                            br_table_current <= 32'h0;
                            state <= STATE_BR_TABLE;
                        end

                        OP_RETURN: begin
                            if (current_frame.return_pc == 32'hFFFFFFFF) begin
                                // Entry function return - capture results then halt
                                capture_result_count <= current_frame.arity;
                                capture_result_idx <= 8'h0;
                                frame_pop_en <= 1'b1;  // Pop entry frame
                                state <= STATE_CAPTURE_RESULTS;
                            end else begin
                                frame_pop_en <= 1'b1;
                                label_set_sp_en <= 1'b1;
                                label_set_sp_value <= current_frame.label_height;
                                pc <= current_frame.return_pc;
                                state <= STATE_FETCH;
                            end
                        end

                        OP_CALL: begin
                            // Check if this is an import function (WASI call)
                            // Convention: code_offset == 0xFFFFFFFF indicates import
                            //             code_length contains the import/WASI function ID
                            if (func_table[saved_decoded.immediate[15:0]].code_offset == 32'hFFFFFFFF) begin
                                // Import call - trap for supervisor handling
                                trap_code <= TRAP_IMPORT;
                                trapped <= 1'b1;
                                // Capture import info
                                import_id_q <= func_table[saved_decoded.immediate[15:0]].code_length[15:0];
                                // Capture arguments from stack (up to 4)
                                // Arguments are on stack: TOS = last arg, deeper = earlier args
                                // operand_a = stack_pop_data = TOS (combinational, always valid)
                                // stack_peek_data uses peek_offset=1, so it's TOS-1
                                // stack_peek_data2 uses peek_offset2=2, so it's TOS-2
                                import_arg0_q <= operand_a.value[31:0];         // TOS (last arg pushed)
                                import_arg1_q <= stack_peek_data.value[31:0];   // TOS-1
                                import_arg2_q <= stack_peek_data2.value[31:0];  // TOS-2
                                // Note: For 4th arg, would need additional peek port
                                import_arg3_q <= 32'h0;
                                state <= STATE_TRAP;
                            end else begin
                                // Normal function call - copy arguments from stack to locals
                                call_func_idx <= saved_decoded.immediate[15:0];
                                call_param_count <= func_table[saved_decoded.immediate[15:0]].param_count;
                                call_arg_idx <= 8'd0;
                                // Initialize peek offset to read the first argument (deepest on stack)
                                // arg0 is at offset (param_count - 1) from TOS
                                call_peek_offset <= {8'b0, func_table[saved_decoded.immediate[15:0]].param_count - 8'd1};
                                // Allocate locals for the called function starting at current position
                                // The arguments will be written starting at this base
                                call_new_local_base <= current_frame.local_base +
                                                       func_table[current_frame.func_idx].param_count +
                                                       func_table[current_frame.func_idx].local_count;
                                state <= STATE_CALL;
                            end
                        end

                        OP_CALL_INDIRECT: begin
                            // Indirect call - operand_a (TOS) is the element index within the table
                            // saved_decoded.immediate = type_index (expected type)
                            // saved_decoded.immediate2 = table_index (which table, 0-3)
                            logic [31:0] elem_idx;
                            logic [15:0] target_func_idx;
                            logic [1:0] which_table;
                            logic [15:0] table_size;

                            elem_idx = operand_a.value[31:0];
                            which_table = saved_decoded.immediate2[1:0];

                            // Get the size of the selected table
                            case (which_table)
                                2'd0: table_size = elem_table_size[0];
                                2'd1: table_size = elem_table_size[1];
                                2'd2: table_size = elem_table_size[2];
                                2'd3: table_size = elem_table_size[3];
                            endcase

                            // Check if element index is out of bounds
                            if (elem_idx >= {16'b0, table_size}) begin
                                trapped <= 1'b1;
                                trap_code <= TRAP_UNDEFINED_ELEMENT;
                                state <= STATE_TRAP;
                            end else begin
                                // Get function index from the selected table
                                case (which_table)
                                    2'd0: target_func_idx = elem_table_0[elem_idx[7:0]];
                                    2'd1: target_func_idx = elem_table_1[elem_idx[7:0]];
                                    2'd2: target_func_idx = elem_table_2[elem_idx[7:0]];
                                    2'd3: target_func_idx = elem_table_3[elem_idx[7:0]];
                                endcase

                                // Check if element is uninitialized
                                if (target_func_idx == 16'hFFFF) begin
                                    trapped <= 1'b1;
                                    trap_code <= TRAP_UNINITIALIZED_ELEMENT;
                                    state <= STATE_TRAP;
                                end else begin
                                    // Structural type check: compare full type signatures
                                    // Expected type from call_indirect instruction
                                    // Actual type from the target function's type_idx
                                    automatic type_entry_t expected_type = type_table[saved_decoded.immediate[7:0]];
                                    automatic type_entry_t actual_type = type_table[func_table[target_func_idx].type_idx[7:0]];

                                    if (expected_type.param_count != actual_type.param_count ||
                                        expected_type.result_count != actual_type.result_count ||
                                        expected_type.param_types != actual_type.param_types ||
                                        expected_type.result_types != actual_type.result_types) begin
                                        // Type mismatch
                                        trapped <= 1'b1;
                                        trap_code <= TRAP_INDIRECT_CALL_TYPE_MISMATCH;
                                        state <= STATE_TRAP;
                                    end else begin
                                        // Pop the element index from stack
                                        stack_pop_en <= 1'b1;

                                        // Set up the call like OP_CALL does
                                        call_func_idx <= target_func_idx;
                                        call_param_count <= func_table[target_func_idx].param_count;
                                        call_arg_idx <= 8'd0;
                                        // Add +1 to initial peek offset because the element index pop
                                        // won't take effect until the next cycle (same cycle as first STATE_CALL)
                                        call_peek_offset <= {8'b0, func_table[target_func_idx].param_count};
                                        call_new_local_base <= current_frame.local_base +
                                                               func_table[current_frame.func_idx].param_count +
                                                               func_table[current_frame.func_idx].local_count;
                                        state <= STATE_CALL;
                                    end
                                end
                            end
                        end

                        // ==== Parametric Instructions ====
                        OP_DROP: begin
                            stack_pop_en <= 1'b1;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_SELECT, OP_SELECT_T: begin
                            // Pop condition and two values, then push selected
                            // Stack: [... val1 val2 cond] -> [..., selected]
                            // operand_a = cond (TOS), operand_b = val2 (TOS-1), operand_c = val1 (TOS-2)
                            // operand_c is already read via stack_peek_data2
                            // OP_SELECT_T is the typed version, but works the same since we track types

                            // Do multi-pop first, then push in writeback
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd3;

                            // Save selected value for push in writeback
                            // WebAssembly select: if cond != 0, return val1, else return val2
                            if (operand_a.value[31:0] != 32'h0) begin
                                exec_result <= operand_c.value;  // Select val1 (deeper)
                                exec_result_type <= operand_c.vtype;
                            end else begin
                                exec_result <= operand_b.value;  // Select val2
                                exec_result_type <= operand_b.vtype;
                            end

                            state <= STATE_WRITEBACK;
                        end

                        // ==== Variable Instructions ====
                        OP_LOCAL_GET: begin
                            local_rd_en <= 1'b1;
                            local_base_idx <= current_frame.local_base;
                            local_idx <= saved_decoded.immediate[7:0];
                            state <= STATE_MEMORY;
                        end

                        OP_LOCAL_SET: begin
                            stack_pop_en <= 1'b1;
                            local_wr_en <= 1'b1;
                            local_wr_base_idx <= current_frame.local_base;
                            local_wr_idx <= saved_decoded.immediate[7:0];
                            local_wr_data <= operand_a;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_LOCAL_TEE: begin
                            // Set local without popping
                            local_wr_en <= 1'b1;
                            local_wr_base_idx <= current_frame.local_base;
                            local_wr_idx <= saved_decoded.immediate[7:0];
                            local_wr_data <= operand_a;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_GLOBAL_GET: begin
                            global_rd_en <= 1'b1;
                            global_rd_idx <= saved_decoded.immediate[7:0];
                            state <= STATE_MEMORY;
                        end

                        OP_GLOBAL_SET: begin
                            stack_pop_en <= 1'b1;
                            global_wr_en <= 1'b1;
                            global_wr_idx <= saved_decoded.immediate[7:0];
                            global_wr_data <= operand_a;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        // ==== Memory Instructions ====
                        OP_I32_LOAD: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I32;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I64_LOAD: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I64;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_F32_LOAD: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_F32;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_F64_LOAD: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_F64;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I32_LOAD8_S: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I8_S;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I32_LOAD8_U: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I8_U;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I32_LOAD16_S: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I16_S;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I32_LOAD16_U: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I16_U;
                                state <= STATE_MEMORY;
                            end
                        end

                        // i64 partial load operations
                        OP_I64_LOAD8_S: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I8_S;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I64_LOAD8_U: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I8_U;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I64_LOAD16_S: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I16_S;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I64_LOAD16_U: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I16_U;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I64_LOAD32_S: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I32_S;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I64_LOAD32_U: begin
                            stack_pop_en <= 1'b1;
                            effective_addr_full = {1'b0, operand_a.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_rd_en <= 1'b1;
                                mem_rd_addr <= effective_addr;
                                mem_rd_op <= MEM_LOAD_I32_U;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_I32_STORE: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I32;
                                mem_wr_data <= operand_a.value;
                                state <= STATE_MEMORY;  // Check for trap
                            end
                        end

                        OP_I64_STORE: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I64;
                                mem_wr_data <= operand_a.value;
                                state <= STATE_MEMORY;  // Check for trap
                            end
                        end

                        OP_I32_STORE8: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I8;
                                mem_wr_data <= {56'b0, operand_a.value[7:0]};
                                state <= STATE_MEMORY;  // Check for trap
                            end
                        end

                        OP_I32_STORE16: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I16;
                                mem_wr_data <= {48'b0, operand_a.value[15:0]};
                                state <= STATE_MEMORY;  // Check for trap
                            end
                        end

                        OP_I64_STORE8: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I8;
                                mem_wr_data <= {56'b0, operand_a.value[7:0]};
                                state <= STATE_MEMORY;  // Check for trap
                            end
                        end

                        OP_I64_STORE16: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I16;
                                mem_wr_data <= {48'b0, operand_a.value[15:0]};
                                state <= STATE_MEMORY;  // Check for trap
                            end
                        end

                        OP_I64_STORE32: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I32_FROM_I64;
                                mem_wr_data <= {32'b0, operand_a.value[31:0]};
                                state <= STATE_MEMORY;  // Check for trap
                            end
                        end

                        OP_F32_STORE: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I32;  // f32 is 32-bit
                                mem_wr_data <= {32'b0, operand_a.value[31:0]};
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_F64_STORE: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            effective_addr_full = {1'b0, operand_b.value[31:0]} + {1'b0, saved_decoded.immediate2};
                            effective_addr_overflow = effective_addr_full[32];
                            effective_addr = effective_addr_full[31:0];
                            if (effective_addr_overflow) begin
                                trap_code <= TRAP_OUT_OF_BOUNDS;
                                state <= STATE_TRAP;
                            end else begin
                                mem_wr_en <= 1'b1;
                                mem_wr_addr <= effective_addr;
                                mem_wr_op <= MEM_STORE_I64;  // f64 is 64-bit
                                mem_wr_data <= operand_a.value;
                                state <= STATE_MEMORY;
                            end
                        end

                        OP_MEMORY_SIZE: begin
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_I32;
                            stack_push_data.value <= {32'b0, mem_current_pages};
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_MEMORY_GROW: begin
                            // If supervisor is connected (ext_halt_i), trap for approval
                            // Otherwise handle locally for standalone operation
                            if (ext_halt_i) begin
                                trap_code <= TRAP_MEMORY_GROW;
                                trapped <= 1'b1;
                                // Store requested pages in import_arg0 for supervisor
                                import_id_q <= 16'h0;  // Not a WASI call
                                import_arg0_q <= operand_a.value[31:0];  // Requested pages
                                import_arg1_q <= mem_current_pages;       // Current pages
                                import_arg2_q <= mem_init_max_pages;      // Max pages (from init)
                                import_arg3_q <= 32'h0;
                                stack_pop_en <= 1'b1;  // Pop the requested pages argument
                                state <= STATE_TRAP;
                            end else begin
                                // Standalone: handle locally
                                stack_pop_en <= 1'b1;
                                mem_grow_en <= 1'b1;
                                mem_grow_pages <= operand_a.value[31:0];
                                state <= STATE_MEMORY;
                            end
                        end

                        // ==== Numeric Constants ====
                        OP_I32_CONST: begin
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_I32;
                            stack_push_data.value <= {{32{saved_decoded.immediate[31]}}, saved_decoded.immediate[31:0]};
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_I64_CONST: begin
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_I64;
                            stack_push_data.value <= saved_decoded.immediate;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_F32_CONST: begin
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_F32;
                            stack_push_data.value <= {32'b0, saved_decoded.immediate[31:0]};
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_F64_CONST: begin
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_F64;
                            stack_push_data.value <= saved_decoded.immediate;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        // ==== i32 Comparison Operations ====
                        OP_I32_EQZ: begin
                            stack_pop_en <= 1'b1;
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_I32;
                            stack_push_data.value <= {63'b0, operand_a.value[31:0] == 32'h0};
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_I32_EQ, OP_I32_NE, OP_I32_LT_S, OP_I32_LT_U,
                        OP_I32_GT_S, OP_I32_GT_U, OP_I32_LE_S, OP_I32_LE_U,
                        OP_I32_GE_S, OP_I32_GE_U: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            alu_i32_valid_in <= 1'b1;
                            alu_i32_a <= operand_b.value[31:0];  // First operand (deeper in stack)
                            alu_i32_b <= operand_a.value[31:0];  // Second operand (TOS)

                            case (saved_decoded.opcode)
                                OP_I32_EQ:   alu_i32_op <= ALU_EQ;
                                OP_I32_NE:   alu_i32_op <= ALU_NE;
                                OP_I32_LT_S: alu_i32_op <= ALU_LT_S;
                                OP_I32_LT_U: alu_i32_op <= ALU_LT_U;
                                OP_I32_GT_S: alu_i32_op <= ALU_GT_S;
                                OP_I32_GT_U: alu_i32_op <= ALU_GT_U;
                                OP_I32_LE_S: alu_i32_op <= ALU_LE_S;
                                OP_I32_LE_U: alu_i32_op <= ALU_LE_U;
                                OP_I32_GE_S: alu_i32_op <= ALU_GE_S;
                                OP_I32_GE_U: alu_i32_op <= ALU_GE_U;
                                default:     alu_i32_op <= ALU_EQ;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        // ==== i32 Unary Operations ====
                        OP_I32_CLZ, OP_I32_CTZ, OP_I32_POPCNT: begin
                            stack_pop_en <= 1'b1;
                            alu_i32_valid_in <= 1'b1;
                            alu_i32_a <= operand_a.value[31:0];
                            alu_i32_b <= 32'h0;

                            case (saved_decoded.opcode)
                                OP_I32_CLZ:    alu_i32_op <= ALU_CLZ;
                                OP_I32_CTZ:    alu_i32_op <= ALU_CTZ;
                                OP_I32_POPCNT: alu_i32_op <= ALU_POPCNT;
                                default:       alu_i32_op <= ALU_CLZ;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        // ==== i32 Binary Operations ====
                        OP_I32_ADD, OP_I32_SUB, OP_I32_MUL, OP_I32_DIV_S, OP_I32_DIV_U,
                        OP_I32_REM_S, OP_I32_REM_U, OP_I32_AND, OP_I32_OR, OP_I32_XOR,
                        OP_I32_SHL, OP_I32_SHR_S, OP_I32_SHR_U, OP_I32_ROTL, OP_I32_ROTR: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            alu_i32_valid_in <= 1'b1;
                            alu_i32_a <= operand_b.value[31:0];
                            alu_i32_b <= operand_a.value[31:0];

                            case (saved_decoded.opcode)
                                OP_I32_ADD:   alu_i32_op <= ALU_ADD;
                                OP_I32_SUB:   alu_i32_op <= ALU_SUB;
                                OP_I32_MUL:   alu_i32_op <= ALU_MUL;
                                OP_I32_DIV_S: alu_i32_op <= ALU_DIV_S;
                                OP_I32_DIV_U: alu_i32_op <= ALU_DIV_U;
                                OP_I32_REM_S: alu_i32_op <= ALU_REM_S;
                                OP_I32_REM_U: alu_i32_op <= ALU_REM_U;
                                OP_I32_AND:   alu_i32_op <= ALU_AND;
                                OP_I32_OR:    alu_i32_op <= ALU_OR;
                                OP_I32_XOR:   alu_i32_op <= ALU_XOR;
                                OP_I32_SHL:   alu_i32_op <= ALU_SHL;
                                OP_I32_SHR_S: alu_i32_op <= ALU_SHR_S;
                                OP_I32_SHR_U: alu_i32_op <= ALU_SHR_U;
                                OP_I32_ROTL:  alu_i32_op <= ALU_ROTL;
                                OP_I32_ROTR:  alu_i32_op <= ALU_ROTR;
                                default:      alu_i32_op <= ALU_ADD;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        // ==== i64 Operations ====
                        OP_I64_EQZ: begin
                            stack_pop_en <= 1'b1;
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_I32;
                            stack_push_data.value <= {63'b0, operand_a.value == 64'h0};
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end

                        OP_I64_EQ, OP_I64_NE, OP_I64_LT_S, OP_I64_LT_U,
                        OP_I64_GT_S, OP_I64_GT_U, OP_I64_LE_S, OP_I64_LE_U,
                        OP_I64_GE_S, OP_I64_GE_U: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            alu_i64_valid_in <= 1'b1;
                            alu_i64_a <= operand_b.value;
                            alu_i64_b <= operand_a.value;

                            case (saved_decoded.opcode)
                                OP_I64_EQ:   alu_i64_op <= ALU_EQ;
                                OP_I64_NE:   alu_i64_op <= ALU_NE;
                                OP_I64_LT_S: alu_i64_op <= ALU_LT_S;
                                OP_I64_LT_U: alu_i64_op <= ALU_LT_U;
                                OP_I64_GT_S: alu_i64_op <= ALU_GT_S;
                                OP_I64_GT_U: alu_i64_op <= ALU_GT_U;
                                OP_I64_LE_S: alu_i64_op <= ALU_LE_S;
                                OP_I64_LE_U: alu_i64_op <= ALU_LE_U;
                                OP_I64_GE_S: alu_i64_op <= ALU_GE_S;
                                OP_I64_GE_U: alu_i64_op <= ALU_GE_U;
                                default:     alu_i64_op <= ALU_EQ;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        OP_I64_CLZ, OP_I64_CTZ, OP_I64_POPCNT: begin
                            stack_pop_en <= 1'b1;
                            alu_i64_valid_in <= 1'b1;
                            alu_i64_a <= operand_a.value;
                            alu_i64_b <= 64'h0;

                            case (saved_decoded.opcode)
                                OP_I64_CLZ:    alu_i64_op <= ALU_CLZ;
                                OP_I64_CTZ:    alu_i64_op <= ALU_CTZ;
                                OP_I64_POPCNT: alu_i64_op <= ALU_POPCNT;
                                default:       alu_i64_op <= ALU_CLZ;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        OP_I64_ADD, OP_I64_SUB, OP_I64_MUL, OP_I64_DIV_S, OP_I64_DIV_U,
                        OP_I64_REM_S, OP_I64_REM_U, OP_I64_AND, OP_I64_OR, OP_I64_XOR,
                        OP_I64_SHL, OP_I64_SHR_S, OP_I64_SHR_U, OP_I64_ROTL, OP_I64_ROTR: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            alu_i64_valid_in <= 1'b1;
                            alu_i64_a <= operand_b.value;
                            alu_i64_b <= operand_a.value;

                            case (saved_decoded.opcode)
                                OP_I64_ADD:   alu_i64_op <= ALU_ADD;
                                OP_I64_SUB:   alu_i64_op <= ALU_SUB;
                                OP_I64_MUL:   alu_i64_op <= ALU_MUL;
                                OP_I64_DIV_S: alu_i64_op <= ALU_DIV_S;
                                OP_I64_DIV_U: alu_i64_op <= ALU_DIV_U;
                                OP_I64_REM_S: alu_i64_op <= ALU_REM_S;
                                OP_I64_REM_U: alu_i64_op <= ALU_REM_U;
                                OP_I64_AND:   alu_i64_op <= ALU_AND;
                                OP_I64_OR:    alu_i64_op <= ALU_OR;
                                OP_I64_XOR:   alu_i64_op <= ALU_XOR;
                                OP_I64_SHL:   alu_i64_op <= ALU_SHL;
                                OP_I64_SHR_S: alu_i64_op <= ALU_SHR_S;
                                OP_I64_SHR_U: alu_i64_op <= ALU_SHR_U;
                                OP_I64_ROTL:  alu_i64_op <= ALU_ROTL;
                                OP_I64_ROTR:  alu_i64_op <= ALU_ROTR;
                                default:      alu_i64_op <= ALU_ADD;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        // ==== f32 Operations ====
                        OP_F32_EQ, OP_F32_NE, OP_F32_LT, OP_F32_GT, OP_F32_LE, OP_F32_GE: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            fpu_f32_valid_in <= 1'b1;
                            fpu_f32_a <= operand_b.value[31:0];
                            fpu_f32_b <= operand_a.value[31:0];

                            case (saved_decoded.opcode)
                                OP_F32_EQ: fpu_f32_op <= FPU_EQ;
                                OP_F32_NE: fpu_f32_op <= FPU_NE;
                                OP_F32_LT: fpu_f32_op <= FPU_LT;
                                OP_F32_GT: fpu_f32_op <= FPU_GT;
                                OP_F32_LE: fpu_f32_op <= FPU_LE;
                                OP_F32_GE: fpu_f32_op <= FPU_GE;
                                default:   fpu_f32_op <= FPU_EQ;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        OP_F32_ABS, OP_F32_NEG, OP_F32_CEIL, OP_F32_FLOOR,
                        OP_F32_TRUNC, OP_F32_NEAREST, OP_F32_SQRT: begin
                            stack_pop_en <= 1'b1;
                            fpu_f32_valid_in <= 1'b1;
                            fpu_f32_a <= operand_a.value[31:0];
                            fpu_f32_b <= 32'h0;

                            case (saved_decoded.opcode)
                                OP_F32_ABS:     fpu_f32_op <= FPU_ABS;
                                OP_F32_NEG:     fpu_f32_op <= FPU_NEG;
                                OP_F32_CEIL:    fpu_f32_op <= FPU_CEIL;
                                OP_F32_FLOOR:   fpu_f32_op <= FPU_FLOOR;
                                OP_F32_TRUNC:   fpu_f32_op <= FPU_TRUNC;
                                OP_F32_NEAREST: fpu_f32_op <= FPU_NEAREST;
                                OP_F32_SQRT:    fpu_f32_op <= FPU_SQRT;
                                default:        fpu_f32_op <= FPU_ABS;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        OP_F32_ADD, OP_F32_SUB, OP_F32_MUL, OP_F32_DIV,
                        OP_F32_MIN, OP_F32_MAX, OP_F32_COPYSIGN: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            fpu_f32_valid_in <= 1'b1;
                            fpu_f32_a <= operand_b.value[31:0];
                            fpu_f32_b <= operand_a.value[31:0];

                            case (saved_decoded.opcode)
                                OP_F32_ADD:      fpu_f32_op <= FPU_ADD;
                                OP_F32_SUB:      fpu_f32_op <= FPU_SUB;
                                OP_F32_MUL:      fpu_f32_op <= FPU_MUL;
                                OP_F32_DIV:      fpu_f32_op <= FPU_DIV;
                                OP_F32_MIN:      fpu_f32_op <= FPU_MIN;
                                OP_F32_MAX:      fpu_f32_op <= FPU_MAX;
                                OP_F32_COPYSIGN: fpu_f32_op <= FPU_COPYSIGN;
                                default:         fpu_f32_op <= FPU_ADD;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        // ==== f64 Operations ====
                        OP_F64_EQ, OP_F64_NE, OP_F64_LT, OP_F64_GT, OP_F64_LE, OP_F64_GE: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            fpu_f64_valid_in <= 1'b1;
                            fpu_f64_a <= operand_b.value;
                            fpu_f64_b <= operand_a.value;

                            case (saved_decoded.opcode)
                                OP_F64_EQ: fpu_f64_op <= FPU_EQ;
                                OP_F64_NE: fpu_f64_op <= FPU_NE;
                                OP_F64_LT: fpu_f64_op <= FPU_LT;
                                OP_F64_GT: fpu_f64_op <= FPU_GT;
                                OP_F64_LE: fpu_f64_op <= FPU_LE;
                                OP_F64_GE: fpu_f64_op <= FPU_GE;
                                default:   fpu_f64_op <= FPU_EQ;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        OP_F64_ABS, OP_F64_NEG, OP_F64_CEIL, OP_F64_FLOOR,
                        OP_F64_TRUNC, OP_F64_NEAREST, OP_F64_SQRT: begin
                            stack_pop_en <= 1'b1;
                            fpu_f64_valid_in <= 1'b1;
                            fpu_f64_a <= operand_a.value;
                            fpu_f64_b <= 64'h0;

                            case (saved_decoded.opcode)
                                OP_F64_ABS:     fpu_f64_op <= FPU_ABS;
                                OP_F64_NEG:     fpu_f64_op <= FPU_NEG;
                                OP_F64_CEIL:    fpu_f64_op <= FPU_CEIL;
                                OP_F64_FLOOR:   fpu_f64_op <= FPU_FLOOR;
                                OP_F64_TRUNC:   fpu_f64_op <= FPU_TRUNC;
                                OP_F64_NEAREST: fpu_f64_op <= FPU_NEAREST;
                                OP_F64_SQRT:    fpu_f64_op <= FPU_SQRT;
                                default:        fpu_f64_op <= FPU_ABS;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        OP_F64_ADD, OP_F64_SUB, OP_F64_MUL, OP_F64_DIV,
                        OP_F64_MIN, OP_F64_MAX, OP_F64_COPYSIGN: begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= 8'd2;
                            fpu_f64_valid_in <= 1'b1;
                            fpu_f64_a <= operand_b.value;
                            fpu_f64_b <= operand_a.value;

                            case (saved_decoded.opcode)
                                OP_F64_ADD:      fpu_f64_op <= FPU_ADD;
                                OP_F64_SUB:      fpu_f64_op <= FPU_SUB;
                                OP_F64_MUL:      fpu_f64_op <= FPU_MUL;
                                OP_F64_DIV:      fpu_f64_op <= FPU_DIV;
                                OP_F64_MIN:      fpu_f64_op <= FPU_MIN;
                                OP_F64_MAX:      fpu_f64_op <= FPU_MAX;
                                OP_F64_COPYSIGN: fpu_f64_op <= FPU_COPYSIGN;
                                default:         fpu_f64_op <= FPU_ADD;
                            endcase
                            state <= STATE_WRITEBACK;
                        end

                        // ==== Conversions ====
                        OP_I32_WRAP_I64, OP_I32_TRUNC_F32_S, OP_I32_TRUNC_F32_U,
                        OP_I32_TRUNC_F64_S, OP_I32_TRUNC_F64_U,
                        OP_I64_EXTEND_I32_S, OP_I64_EXTEND_I32_U,
                        OP_I64_TRUNC_F32_S, OP_I64_TRUNC_F32_U,
                        OP_I64_TRUNC_F64_S, OP_I64_TRUNC_F64_U,
                        OP_F32_CONVERT_I32_S, OP_F32_CONVERT_I32_U,
                        OP_F32_CONVERT_I64_S, OP_F32_CONVERT_I64_U,
                        OP_F32_DEMOTE_F64,
                        OP_F64_CONVERT_I32_S, OP_F64_CONVERT_I32_U,
                        OP_F64_CONVERT_I64_S, OP_F64_CONVERT_I64_U,
                        OP_F64_PROMOTE_F32,
                        OP_I32_REINTERPRET_F32, OP_I64_REINTERPRET_F64,
                        OP_F32_REINTERPRET_I32, OP_F64_REINTERPRET_I64,
                        OP_I32_EXTEND8_S, OP_I32_EXTEND16_S,
                        OP_I64_EXTEND8_S, OP_I64_EXTEND16_S, OP_I64_EXTEND32_S: begin
                            stack_pop_en <= 1'b1;
                            conv_valid_in <= 1'b1;
                            conv_op <= saved_decoded.opcode;
                            conv_operand <= operand_a.value;
                            state <= STATE_WRITEBACK;
                        end

                        // Extended opcodes (0xFC prefix) - trunc_sat
                        OP_PREFIX_FC: begin
                            // immediate[7:0] contains the sub-opcode
                            // 0x00-0x07 are trunc_sat operations
                            if (saved_decoded.immediate[7:0] <= 8'd7) begin
                                stack_pop_en <= 1'b1;
                                conv_valid_in <= 1'b1;
                                conv_op <= OP_PREFIX_FC;
                                conv_sub_op <= saved_decoded.immediate[7:0];
                                conv_operand <= operand_a.value;
                                state <= STATE_WRITEBACK;
                            end else begin
                                // Other 0xFC opcodes not implemented
                                pc <= saved_next_pc;
                                state <= STATE_FETCH;
                            end
                        end

                        default: begin
                            // Unknown opcode - just skip
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end
                    endcase
                end

                STATE_MEMORY: begin
                    // Wait for memory operations
                    if (local_rd_valid) begin
                        stack_push_en <= 1'b1;
                        stack_push_data <= local_rd_data;
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                    else if (global_rd_valid) begin
                        stack_push_en <= 1'b1;
                        stack_push_data <= global_rd_data;
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                    else if (mem_rd_valid) begin
                        stack_push_en <= 1'b1;
                        case (saved_decoded.opcode)
                            OP_I32_LOAD, OP_I32_LOAD8_S, OP_I32_LOAD8_U,
                            OP_I32_LOAD16_S, OP_I32_LOAD16_U: begin
                                stack_push_data.vtype <= TYPE_I32;
                            end
                            OP_I64_LOAD, OP_I64_LOAD8_S, OP_I64_LOAD8_U,
                            OP_I64_LOAD16_S, OP_I64_LOAD16_U,
                            OP_I64_LOAD32_S, OP_I64_LOAD32_U: begin
                                stack_push_data.vtype <= TYPE_I64;
                            end
                            OP_F32_LOAD: begin
                                stack_push_data.vtype <= TYPE_F32;
                            end
                            OP_F64_LOAD: begin
                                stack_push_data.vtype <= TYPE_F64;
                            end
                            default: stack_push_data.vtype <= TYPE_I32;
                        endcase
                        stack_push_data.value <= mem_rd_data;
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                    else if (mem_wr_valid) begin
                        // Memory write completed successfully
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                    else if (mem_trap != TRAP_NONE) begin
                        trapped <= 1'b1;
                        trap_code <= mem_trap;
                        state <= STATE_TRAP;
                    end
                    else if (saved_decoded.opcode == OP_MEMORY_GROW && !mem_grow_en) begin
                        // Memory grow result ready (wait one cycle after grow_en deasserted)
                        stack_push_en <= 1'b1;
                        stack_push_data.vtype <= TYPE_I32;
                        stack_push_data.value <= {32'b0, mem_grow_result};
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                end

                STATE_WRITEBACK: begin
                    // Push ALU/FPU results to stack
                    stack_push_en <= 1'b1;

                    if (alu_i32_valid_out) begin
                        if (alu_i32_trap != TRAP_NONE) begin
                            trapped <= 1'b1;
                            trap_code <= alu_i32_trap;
                            state <= STATE_TRAP;
                        end else begin
                            stack_push_data.vtype <= TYPE_I32;
                            stack_push_data.value <= {32'b0, alu_i32_result};
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end
                    end
                    else if (alu_i64_valid_out) begin
                        if (alu_i64_trap != TRAP_NONE) begin
                            trapped <= 1'b1;
                            trap_code <= alu_i64_trap;
                            state <= STATE_TRAP;
                        end else begin
                            // i64 comparison returns i32
                            case (saved_decoded.opcode)
                                OP_I64_EQ, OP_I64_NE, OP_I64_LT_S, OP_I64_LT_U,
                                OP_I64_GT_S, OP_I64_GT_U, OP_I64_LE_S, OP_I64_LE_U,
                                OP_I64_GE_S, OP_I64_GE_U: begin
                                    stack_push_data.vtype <= TYPE_I32;
                                    stack_push_data.value <= {32'b0, alu_i64_result[31:0]};
                                end
                                default: begin
                                    stack_push_data.vtype <= TYPE_I64;
                                    stack_push_data.value <= alu_i64_result;
                                end
                            endcase
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end
                    end
                    else if (fpu_f32_valid_out) begin
                        // f32 comparison returns i32
                        case (saved_decoded.opcode)
                            OP_F32_EQ, OP_F32_NE, OP_F32_LT, OP_F32_GT, OP_F32_LE, OP_F32_GE: begin
                                stack_push_data.vtype <= TYPE_I32;
                                stack_push_data.value <= {32'b0, fpu_f32_result};
                            end
                            default: begin
                                stack_push_data.vtype <= TYPE_F32;
                                stack_push_data.value <= {32'b0, fpu_f32_result};
                            end
                        endcase
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                    else if (fpu_f64_valid_out) begin
                        // f64 comparison returns i32
                        case (saved_decoded.opcode)
                            OP_F64_EQ, OP_F64_NE, OP_F64_LT, OP_F64_GT, OP_F64_LE, OP_F64_GE: begin
                                stack_push_data.vtype <= TYPE_I32;
                                stack_push_data.value <= {32'b0, fpu_f64_result[31:0]};
                            end
                            default: begin
                                stack_push_data.vtype <= TYPE_F64;
                                stack_push_data.value <= fpu_f64_result;
                            end
                        endcase
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                    else if (conv_valid_out) begin
                        if (conv_trap != TRAP_NONE) begin
                            trapped <= 1'b1;
                            trap_code <= conv_trap;
                            state <= STATE_TRAP;
                        end else begin
                            case (saved_decoded.opcode)
                                OP_I32_WRAP_I64, OP_I32_TRUNC_F32_S, OP_I32_TRUNC_F32_U,
                                OP_I32_TRUNC_F64_S, OP_I32_TRUNC_F64_U,
                                OP_I32_REINTERPRET_F32, OP_I32_EXTEND8_S, OP_I32_EXTEND16_S: begin
                                    stack_push_data.vtype <= TYPE_I32;
                                end
                                OP_I64_EXTEND_I32_S, OP_I64_EXTEND_I32_U,
                                OP_I64_TRUNC_F32_S, OP_I64_TRUNC_F32_U,
                                OP_I64_TRUNC_F64_S, OP_I64_TRUNC_F64_U,
                                OP_I64_REINTERPRET_F64, OP_I64_EXTEND8_S,
                                OP_I64_EXTEND16_S, OP_I64_EXTEND32_S: begin
                                    stack_push_data.vtype <= TYPE_I64;
                                end
                                OP_F32_CONVERT_I32_S, OP_F32_CONVERT_I32_U,
                                OP_F32_CONVERT_I64_S, OP_F32_CONVERT_I64_U,
                                OP_F32_DEMOTE_F64, OP_F32_REINTERPRET_I32: begin
                                    stack_push_data.vtype <= TYPE_F32;
                                end
                                OP_F64_CONVERT_I32_S, OP_F64_CONVERT_I32_U,
                                OP_F64_CONVERT_I64_S, OP_F64_CONVERT_I64_U,
                                OP_F64_PROMOTE_F32, OP_F64_REINTERPRET_I64: begin
                                    stack_push_data.vtype <= TYPE_F64;
                                end
                                OP_PREFIX_FC: begin
                                    // trunc_sat: sub_op 0-3 return i32, 4-7 return i64
                                    if (conv_sub_op <= 8'd3)
                                        stack_push_data.vtype <= TYPE_I32;
                                    else
                                        stack_push_data.vtype <= TYPE_I64;
                                end
                                default: stack_push_data.vtype <= TYPE_I32;
                            endcase
                            stack_push_data.value <= conv_result;
                            pc <= saved_next_pc;
                            state <= STATE_FETCH;
                        end
                    end
                    else if (saved_decoded.opcode == OP_SELECT || saved_decoded.opcode == OP_SELECT_T) begin
                        // Select instruction - push the pre-computed result
                        stack_push_data.vtype <= exec_result_type;
                        stack_push_data.value <= exec_result;
                        pc <= saved_next_pc;
                        state <= STATE_FETCH;
                    end
                end

                STATE_CALL: begin
                    // Copy arguments from operand stack to locals for called function
                    // Pipeline: cycle N reads arg[N], cycle N+1 writes arg[N]
                    // Arguments are on stack: [..., arg0, arg1, arg2] where arg2 is TOS (offset 0)
                    // arg[i] is at peek_offset = param_count - 1 - i
                    //
                    // Cycle 0: peek arg0 (offset = param_count-1), set up for arg1
                    // Cycle 1: save arg0, peek arg1, write nothing yet
                    // Cycle 2: write arg0, save arg1, peek arg2...
                    // etc.

                    // Save current peeked value
                    call_saved_arg <= stack_peek_data;

                    if (call_arg_idx < call_param_count) begin
                        // Write previously saved argument (except on first cycle)
                        if (call_arg_idx > 0) begin
                            local_wr_en <= 1'b1;
                            local_wr_base_idx <= call_new_local_base;
                            local_wr_idx <= call_arg_idx - 8'd1;
                            local_wr_data <= call_saved_arg;
                        end

                        // Update peek offset for next argument
                        if (call_arg_idx + 8'd1 < call_param_count) begin
                            call_peek_offset <= {8'b0, call_param_count - 8'd2 - call_arg_idx};
                        end
                        call_arg_idx <= call_arg_idx + 8'd1;
                    end else begin
                        // Write the last saved argument (if any)
                        if (call_param_count > 0) begin
                            local_wr_en <= 1'b1;
                            local_wr_base_idx <= call_new_local_base;
                            local_wr_idx <= call_param_count - 8'd1;
                            local_wr_data <= call_saved_arg;
                        end

                        // Pop arguments from stack
                        if (call_param_count > 0) begin
                            stack_multi_pop_en <= 1'b1;
                            stack_multi_pop_count <= call_param_count;
                        end

                        // Push call frame
                        frame_push_en <= 1'b1;
                        frame_push_data.return_pc <= saved_next_pc;
                        frame_push_data.func_idx <= call_func_idx;
                        frame_push_data.local_base <= call_new_local_base;
                        frame_push_data.stack_height <= stack_ptr - {8'b0, call_param_count};
                        frame_push_data.label_height <= label_stack_ptr;
                        frame_push_data.arity <= func_table[call_func_idx].result_count;

                        // Jump to function
                        pc <= func_table[call_func_idx].code_offset;
                        state <= STATE_FETCH;
                    end
                end

                STATE_SCAN_ELSE: begin
                    // Scan for else or end opcode (for if with false condition)
                    // Use decoder to get instruction length
                    logic [7:0] scan_byte;
                    logic [31:0] skip_len;
                    scan_byte = code_mem[pc];

                    // Calculate skip length based on opcode
                    case (scan_byte)
                        8'h02, 8'h03, 8'h04: begin  // block, loop, if - increment depth
                            scan_depth <= scan_depth + 1;
                            skip_len = 2;  // opcode + blocktype
                        end
                        8'h05: begin  // else
                            if (scan_depth == 0) begin
                                // Found matching else - enter else block
                                label_push_en <= 1'b1;
                                label_push_data.target_pc <= 32'h0;
                                label_push_data.stack_height <= stack_ptr;
                                // Determine block arity from block type (same logic as OP_IF)
                                if (saved_decoded.immediate == 64'hFFFFFFFF)
                                    label_push_data.arity <= 8'h0;
                                else if (saved_decoded.immediate >= 64'h7C && saved_decoded.immediate <= 64'h7F)
                                    label_push_data.arity <= 8'h1;
                                else
                                    label_push_data.arity <= type_table[saved_decoded.immediate[7:0]].result_count;
                                label_push_data.is_loop <= 1'b0;
                                pc <= pc + 1;
                                state <= STATE_FETCH;
                            end else begin
                                pc <= pc + 1;
                            end
                            skip_len = 0;  // Handled above
                        end
                        8'h0B: begin  // end - decrement depth or found target
                            if (scan_depth == 0) begin
                                pc <= pc + 1;
                                state <= STATE_FETCH;
                            end else begin
                                scan_depth <= scan_depth - 1;
                                pc <= pc + 1;
                            end
                            skip_len = 0;
                        end
                        // Instructions with LEB128 immediate
                        8'h0C, 8'h0D: skip_len = 2;  // br, br_if (assume small label)
                        8'h10: skip_len = 2;  // call (assume small index)
                        8'h20, 8'h21, 8'h22, 8'h23, 8'h24: skip_len = 2;  // local/global ops
                        8'h41: skip_len = 2;  // i32.const (assume small value)
                        8'h42: skip_len = 2;  // i64.const (assume small value)
                        8'h43: skip_len = 5;  // f32.const
                        8'h44: skip_len = 9;  // f64.const
                        8'h28, 8'h29, 8'h2A, 8'h2B, 8'h2C, 8'h2D, 8'h2E, 8'h2F,
                        8'h30, 8'h31, 8'h32, 8'h33, 8'h34, 8'h35, 8'h36, 8'h37,
                        8'h38, 8'h39, 8'h3A, 8'h3B, 8'h3C, 8'h3D, 8'h3E: skip_len = 3;  // memory ops (align + offset)
                        8'h3F, 8'h40: skip_len = 2;  // memory.size, memory.grow (single memidx)
                        default: skip_len = 1;  // Simple opcodes
                    endcase

                    if (skip_len != 0) pc <= pc + skip_len;
                end

                STATE_SCAN_END: begin
                    // Scan for end opcode (for else block skip)
                    logic [7:0] scan_byte;
                    logic [31:0] skip_len;
                    scan_byte = code_mem[pc];

                    case (scan_byte)
                        8'h02, 8'h03, 8'h04: begin  // block, loop, if
                            scan_depth <= scan_depth + 1;
                            skip_len = 2;
                        end
                        8'h0B: begin  // end
                            if (scan_depth == 0) begin
                                pc <= pc + 1;
                                // Check if we need stack unwinding (branch) or not (else-skip)
                                if (scan_needs_unwind) begin
                                    state <= STATE_BR_UNWIND;
                                end else begin
                                    state <= STATE_FETCH;
                                end
                            end else begin
                                scan_depth <= scan_depth - 1;
                                pc <= pc + 1;
                            end
                            skip_len = 0;
                        end
                        8'h05: skip_len = 1;  // else (increment depth is implicit in if)
                        8'h0C, 8'h0D: skip_len = 2;  // br, br_if
                        8'h0E: begin  // br_table - variable length, need to scan
                            // Switch to br_table scan state
                            scan_br_table_start <= pc + 1;  // Start of count
                            scan_br_table_remaining <= 32'hFFFFFFFF;  // Signal to read count
                            state <= STATE_SCAN_BR_TABLE;
                            skip_len = 0;
                        end
                        8'h10: skip_len = 2;
                        8'h20, 8'h21, 8'h22, 8'h23, 8'h24: skip_len = 2;
                        8'h41: skip_len = 2;
                        8'h42: skip_len = 2;
                        8'h43: skip_len = 5;
                        8'h44: skip_len = 9;
                        8'h28, 8'h29, 8'h2A, 8'h2B, 8'h2C, 8'h2D, 8'h2E, 8'h2F,
                        8'h30, 8'h31, 8'h32, 8'h33, 8'h34, 8'h35, 8'h36, 8'h37,
                        8'h38, 8'h39, 8'h3A, 8'h3B, 8'h3C, 8'h3D, 8'h3E: skip_len = 3;
                        8'h3F, 8'h40: skip_len = 2;  // memory.size, memory.grow (single memidx)
                        default: skip_len = 1;
                    endcase

                    if (skip_len != 0) pc <= pc + skip_len;
                end

                STATE_SCAN_BR_TABLE: begin
                    // Scan through br_table to skip past it during STATE_SCAN_END
                    // We need to skip: count (LEB128) + count * target_depth (LEB128) + default (LEB128)
                    logic [7:0] sbt_byte;
                    logic [31:0] sbt_count;
                    logic [31:0] sbt_leb_len;

                    sbt_byte = code_mem[scan_br_table_start];

                    // Simple LEB128 decode for count
                    if ((sbt_byte & 8'h80) == 0) begin
                        sbt_count = {24'b0, sbt_byte};
                        sbt_leb_len = 1;
                    end else begin
                        sbt_count = {17'b0, code_mem[scan_br_table_start + 1][6:0], sbt_byte[6:0]};
                        sbt_leb_len = 2;
                    end

                    // First call: read count and set up for scanning targets
                    if (scan_br_table_remaining == 32'hFFFFFFFF) begin
                        scan_br_table_remaining <= sbt_count + 1;  // count targets + 1 default
                        scan_br_table_start <= scan_br_table_start + sbt_leb_len;
                    end else if (scan_br_table_remaining == 0) begin
                        // Done - return to STATE_SCAN_END
                        pc <= scan_br_table_start;
                        state <= STATE_SCAN_END;
                    end else begin
                        // Skip one LEB128 target depth
                        if ((sbt_byte & 8'h80) == 0) begin
                            scan_br_table_start <= scan_br_table_start + 1;
                        end else begin
                            scan_br_table_start <= scan_br_table_start + 2;
                        end
                        scan_br_table_remaining <= scan_br_table_remaining - 1;
                    end
                end

                STATE_BR_TABLE: begin
                    // Process br_table targets
                    // Read LEB128 target depth from code_mem[br_table_pc]
                    logic [7:0] leb_byte0, leb_byte1;
                    logic [31:0] target_depth;
                    logic [31:0] leb_len;

                    leb_byte0 = code_mem[br_table_pc];
                    leb_byte1 = code_mem[br_table_pc + 1];

                    // Simple LEB128 decode (handles up to 2 bytes, values up to 16383)
                    if ((leb_byte0 & 8'h80) == 0) begin
                        target_depth = {24'b0, leb_byte0};
                        leb_len = 1;
                    end else begin
                        target_depth = {17'b0, leb_byte1[6:0], leb_byte0[6:0]};
                        leb_len = 2;
                    end

                    // State machine for br_table processing
                    if (br_table_current > br_table_count) begin
                        // Phase 3: All targets processed, now branch
                        // Check if branch targets function level
                        logic [7:0] brt_func_label_count;
                        logic brt_is_func_return;
                        brt_func_label_count = label_stack_ptr - current_frame.label_height;
                        brt_is_func_return = (br_table_depth >= brt_func_label_count);

                        if (brt_is_func_return) begin
                            // Branch to function block = return
                            label_set_sp_en <= 1'b1;
                            label_set_sp_value <= current_frame.label_height;
                            branch_target_stack_height <= current_frame.stack_height;
                            branch_target_arity <= current_frame.arity;
                            branch_target_pc <= 32'hFFFFFFFF;
                            // Save branch value (TOS) for STATE_BR_UNWIND
                            branch_saved_value <= stack_pop_data;
                            state <= STATE_BR_UNWIND;
                        end else begin
                            // Save target info for stack unwinding
                            branch_target_stack_height <= label_branch_target.stack_height;
                            branch_target_arity <= label_branch_target.arity;
                            branch_target_pc <= label_branch_target.target_pc;

                            if (label_branch_target.is_loop) begin
                                // Loop: pop intermediate labels but keep loop's label
                                if (br_table_depth > 0) begin
                                    label_set_sp_en <= 1'b1;
                                    label_set_sp_value <= label_stack_ptr - br_table_depth;
                                end
                                pc <= label_branch_target.target_pc;
                                state <= STATE_FETCH;
                            end else begin
                                // Block: pop labels including target block
                                label_branch_pop_en <= 1'b1;
                                // Block - scan forward to find END
                                scan_depth <= br_table_depth;
                                scan_for_else <= 1'b0;
                                scan_needs_unwind <= 1'b1;
                                pc <= br_table_pc;
                                state <= STATE_SCAN_END;
                            end
                        end
                    end else if (br_table_current == br_table_count) begin
                        // Phase 2: At the default target - this is the last one
                        // Set br_table_depth to the final value we'll use
                        if (br_table_index >= br_table_count) begin
                            // Use default
                            br_table_depth <= target_depth[7:0];
                        end
                        // If index < count, br_table_depth was already set, keep it

                        // Save PC after br_table for next cycle
                        br_table_pc <= br_table_pc + leb_len;
                        br_table_current <= br_table_current + 1;
                    end else begin
                        // Phase 1: Scanning through targets
                        // Check if we've found the target we want
                        if (br_table_current == br_table_index) begin
                            // Found our target - save the depth
                            br_table_depth <= target_depth[7:0];
                        end
                        // Move to next target
                        br_table_pc <= br_table_pc + leb_len;
                        br_table_current <= br_table_current + 1;
                    end
                end

                STATE_BR_UNWIND: begin
                    // Unwind stack after branch to match target label's stack height
                    // For arity > 0, we need to keep the top arity values
                    // Uses phases: normal (compute), 0xFE (multi-value save), 0xFF (restore)
                    logic need_collapse;
                    logic [15:0] excess_values;
                    logic is_func_return;
                    logic [15:0] effective_sp;

                    // Check if this is a branch to function block (return)
                    is_func_return = (branch_target_pc == 32'hFFFFFFFF);

                    // Adjust stack_ptr for pending pop from br_if
                    effective_sp = branch_pop_pending ? (stack_ptr - 1) : stack_ptr;
                    excess_values = effective_sp - branch_target_stack_height;
                    need_collapse = (branch_target_arity > 0) && (branch_target_arity < 8'hFD) &&
                                    (excess_values > {8'b0, branch_target_arity});

                    if (branch_target_arity == 8'hFD) begin
                        // First cycle of save phase: just transition, peek offset now correct
                        // On next cycle, branch_target_arity will be 0xFE and peek works
                        branch_target_arity <= 8'hFE;
                    end else if (branch_target_arity == 8'hFE) begin
                        // Multi-value save phase: save values one by one
                        // peek_offset is set combinationally based on branch_mv_idx + pop_pending offset
                        branch_saved_values[branch_mv_idx] <= stack_peek_data;

                        if (branch_mv_idx + 8'd1 >= branch_mv_arity) begin
                            // All values saved, collapse stack and enter restore phase
                            branch_pop_pending <= 1'b0;
                            stack_set_sp_en <= 1'b1;
                            stack_set_sp_value <= branch_target_stack_height;
                            branch_target_arity <= 8'hFF;  // Enter restore phase
                            branch_mv_idx <= 8'h0;
                        end else begin
                            branch_mv_idx <= branch_mv_idx + 8'd1;
                        end
                    end else if (branch_target_arity == 8'hFF) begin
                        // Restore phase: push saved values back (or copy to results for function return)
                        if (is_func_return) begin
                            // Function return - copy saved values to result_values
                            // branch_saved_values[0] = TOS, [1] = TOS-1, etc.
                            // result_values[0] = bottom result, [N-1] = top result
                            // So result_values[i] = branch_saved_values[arity-1-i]
                            if (branch_mv_idx < branch_mv_arity) begin
                                result_values[branch_mv_arity - 8'd1 - branch_mv_idx] <= branch_saved_values[branch_mv_idx];
                                branch_mv_idx <= branch_mv_idx + 8'd1;
                            end else begin
                                // All results copied
                                result_value <= result_values[0];
                                result_valid <= 1'b1;
                                result_count <= branch_mv_arity;
                                halted <= 1'b1;
                                branch_target_arity <= 8'h0;
                                state <= STATE_HALT;
                            end
                        end else begin
                            // Non-return branch - push values back to stack
                            // Push in reverse order: branch_saved_values[arity-1] first, [0] last
                            if (branch_mv_idx < branch_mv_arity) begin
                                stack_push_en <= 1'b1;
                                stack_push_data <= branch_saved_values[branch_mv_arity - 8'd1 - branch_mv_idx];
                                branch_mv_idx <= branch_mv_idx + 8'd1;
                            end else begin
                                // All values pushed back
                                branch_target_arity <= 8'h0;
                                state <= STATE_FETCH;
                            end
                        end
                    end else if (need_collapse) begin
                        // Need to collapse stack - check if multi-value or single-value
                        if (branch_target_arity > 8'd1) begin
                            // Multi-value: enter save phase (0xFD is setup, 0xFE is active saving)
                            branch_mv_arity <= branch_target_arity;
                            branch_mv_idx <= 8'h0;
                            branch_target_arity <= 8'hFD;  // Enter save phase setup
                            // Don't clear pop_pending yet - needed for peek offset calculation
                        end else begin
                            // Single value (arity == 1): use original fast path
                            if (!branch_pop_pending) begin
                                branch_saved_value <= stack_pop_data;
                                branch_saved_values[0] <= stack_pop_data;
                            end else begin
                                // Value already saved in branch_saved_value by br_if
                                branch_saved_values[0] <= branch_saved_value;
                            end
                            branch_pop_pending <= 1'b0;
                            stack_set_sp_en <= 1'b1;
                            stack_set_sp_value <= branch_target_stack_height;
                            branch_target_arity <= 8'hFF;  // Flag for phase 2
                            branch_mv_arity <= 8'd1;  // Mark as single-value restore
                            branch_mv_idx <= 8'h0;    // Initialize index for restore phase
                        end
                    end else if (branch_target_arity == 0 && effective_sp > branch_target_stack_height) begin
                        // Void block with extra values - restore stack height
                        branch_pop_pending <= 1'b0;
                        stack_set_sp_en <= 1'b1;
                        stack_set_sp_value <= branch_target_stack_height;
                        if (is_func_return) begin
                            capture_result_count <= 8'h0;
                            capture_result_idx <= 8'h0;
                            state <= STATE_CAPTURE_RESULTS;
                        end else begin
                            state <= STATE_FETCH;
                        end
                    end else begin
                        // Stack already correct or arity matches excess
                        branch_pop_pending <= 1'b0;
                        if (is_func_return) begin
                            capture_result_count <= branch_target_arity;
                            capture_result_idx <= 8'h0;
                            state <= STATE_CAPTURE_RESULTS;
                        end else begin
                            state <= STATE_FETCH;
                        end
                    end
                end

                STATE_CAPTURE_RESULTS: begin
                    // Capture multi-value results from stack before halting
                    // Results are on stack: result[0] at bottom, result[N-1] at TOS
                    // stack_peek_offset is set by combinational logic based on capture_result_idx
                    // Peek is combinational, so store on same cycle as peek
                    if (capture_result_count == 0) begin
                        // No results to capture - just halt
                        result_valid <= 1'b1;
                        result_count <= 8'h0;
                        halted <= 1'b1;
                        state <= STATE_HALT;
                    end else if (capture_result_idx < capture_result_count) begin
                        // Stack peek is happening combinationally based on capture_result_idx
                        // peek_offset=0 -> TOS -> result[N-1]
                        // peek_offset=i -> result[N-1-i]
                        // Store at: result_values[N-1-i] = stack_peek_data
                        result_values[capture_result_count - 8'd1 - capture_result_idx] <= stack_peek_data;
                        capture_result_idx <= capture_result_idx + 1;
                    end else begin
                        // All results captured, set final outputs and halt
                        // result_value is for backward compatibility (first result = result[0])
                        result_value <= result_values[0];
                        result_valid <= 1'b1;
                        result_count <= capture_result_count;
                        halted <= 1'b1;
                        state <= STATE_HALT;
                    end
                end

                STATE_TRAP: begin
                    // Trap occurred - check if supervisor wants to handle it
                    trapped <= 1'b1;
                    halted <= 1'b1;

                    if (ext_halt_i && (trap_code == TRAP_IMPORT || trap_code == TRAP_MEMORY_GROW)) begin
                        // Supervisor is connected and wants to handle this trap
                        // Transition to EXT_HALT to wait for resume
                        state <= STATE_EXT_HALT;
                    end else if (start) begin
                        // Restart execution at entry function (no supervisor handling)
                        pc <= func_table[entry_func].code_offset;
                        state <= STATE_FETCH;
                        halted <= 1'b0;
                        trapped <= 1'b0;

                        // Push implicit call frame for the entry function
                        // Use current stack_ptr as local_base - args are already on stack
                        frame_push_en <= 1'b1;
                        frame_push_data.return_pc <= 32'hFFFFFFFF;  // Special: no return
                        frame_push_data.func_idx <= entry_func[15:0];
                        frame_push_data.local_base <= stack_ptr;
                        frame_push_data.stack_height <= stack_ptr;
                        frame_push_data.label_height <= 8'h0;
                        frame_push_data.arity <= func_table[entry_func].result_count;
                    end
                end

                STATE_HALT: begin
                    // Stay halted, but allow restart
                    if (start) begin
                        // Start execution at entry function
                        pc <= func_table[entry_func].code_offset;
                        state <= STATE_FETCH;
                        halted <= 1'b0;
                        trapped <= 1'b0;

                        // Push implicit call frame for the entry function
                        // Use current stack_ptr as local_base - args are already on stack
                        frame_push_en <= 1'b1;
                        frame_push_data.return_pc <= 32'hFFFFFFFF;  // Special: no return
                        frame_push_data.func_idx <= entry_func[15:0];
                        frame_push_data.local_base <= stack_ptr;
                        frame_push_data.stack_height <= stack_ptr;
                        frame_push_data.label_height <= 8'h0;
                        frame_push_data.arity <= func_table[entry_func].result_count;
                    end
                end

                STATE_EXT_HALT: begin
                    // Externally halted, waiting for supervisor to resume
                    // Import trap info is captured in import_*_q registers
                    if (ext_resume_i) begin
                        // Resume execution - supervisor has handled the trap
                        // If resume_pc is non-zero, use it; otherwise continue from trap PC
                        if (ext_resume_pc_i != '0) begin
                            pc <= ext_resume_pc_i;
                        end
                        // If resume_val is provided, push it on stack (for return values)
                        if (ext_resume_val_i != '0 || trap_code == TRAP_IMPORT) begin
                            stack_push_en <= 1'b1;
                            stack_push_data.vtype <= TYPE_I32;
                            stack_push_data.value <= {32'b0, ext_resume_val_i};
                        end
                        state <= STATE_FETCH;
                        halted <= 1'b0;
                        trapped <= 1'b0;
                        trap_code <= TRAP_NONE;
                    end else if (start) begin
                        // Allow full restart as an alternative to resume
                        pc <= func_table[entry_func].code_offset;
                        state <= STATE_FETCH;
                        halted <= 1'b0;
                        trapped <= 1'b0;
                        trap_code <= TRAP_NONE;
                        frame_push_en <= 1'b1;
                        frame_push_data.return_pc <= 32'hFFFFFFFF;
                        frame_push_data.func_idx <= entry_func[15:0];
                        frame_push_data.local_base <= stack_ptr;
                        frame_push_data.stack_height <= stack_ptr;
                        frame_push_data.label_height <= 8'h0;
                        frame_push_data.arity <= func_table[entry_func].result_count;
                    end
                end

                default: begin
                    state <= STATE_IDLE;
                end
            endcase
        end
    end

    // =========================================================================
    // External Halt/Resume Interface Outputs
    // =========================================================================

    // CPU is externally halted when in STATE_EXT_HALT or transitioning to it
    assign ext_halted_o = (state == STATE_EXT_HALT) ||
                          (state == STATE_TRAP && ext_halt_i &&
                           (trap_code == TRAP_IMPORT || trap_code == TRAP_MEMORY_GROW));

    // Import trap information outputs
    assign import_id_o   = import_id_q;
    assign import_arg0_o = import_arg0_q;
    assign import_arg1_o = import_arg1_q;
    assign import_arg2_o = import_arg2_q;
    assign import_arg3_o = import_arg3_q;

endmodule
