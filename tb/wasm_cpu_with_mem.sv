// WebAssembly CPU with Memory Wrapper
// This module wraps wasm_cpu and wasm_memory together for standalone testing.
// Used by C++ testbenches (cpu_trap_test, firmware_test, etc.) that need
// direct access to a complete CPU+memory system.

module wasm_cpu_with_mem
    import wasm_pkg::*;
#(
    parameter int CODE_SIZE = 65536,
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

    // Code memory interface
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
    input  logic [31:0] mem_init_max_pages,

    // Memory data initialization interface
    input  logic        mem_data_wr_en,
    input  logic [31:0] mem_data_wr_addr,
    input  logic [7:0]  mem_data_wr_data,

    // Stack initialization interface
    input  logic        stack_init_en,
    input  stack_entry_t stack_init_data,

    // Stack reset interface
    input  logic        stack_reset_en,

    // Locals initialization interface
    input  logic        local_init_wr_en,
    input  logic [15:0] local_init_wr_base,
    input  logic [7:0]  local_init_wr_idx,
    input  stack_entry_t local_init_wr_data,

    // Global initialization interface
    input  logic        global_init_en,
    input  logic [7:0]  global_init_idx,
    input  global_entry_t global_init_data,

    // Element table initialization interface
    input  logic        elem_init_en,
    input  logic [1:0]  elem_init_table_idx,
    input  logic [15:0] elem_init_idx,
    input  logic [15:0] elem_init_func_idx,

    // Type table initialization interface
    input  logic        type_init_en,
    input  logic [7:0]  type_init_idx,
    input  logic [7:0]  type_init_param_count,
    input  logic [7:0]  type_init_result_count,
    input  logic [31:0] type_init_param_types,
    input  logic [31:0] type_init_result_types,

    // Result output
    output logic        result_valid,
    output stack_entry_t result_value,
    output logic [7:0]  result_count,
    output stack_entry_t result_values [0:15],

    // Debug interface
    output logic [31:0] dbg_pc,
    output exec_state_t dbg_state,
    output logic [15:0] dbg_stack_ptr,
    output logic [31:0] dbg_saved_next_pc,
    output logic [31:0] dbg_decode_next_pc,
    output logic [7:0]  dbg_instr_len,

    // External halt/resume interface
    input  logic        ext_halt_i,
    input  logic        ext_resume_i,
    input  logic [31:0] ext_resume_pc_i,
    input  logic [31:0] ext_resume_val_i,
    output logic        ext_halted_o,

    // Import trap information
    output logic [15:0] import_id_o,
    output logic [31:0] import_arg0_o,
    output logic [31:0] import_arg1_o,
    output logic [31:0] import_arg2_o,
    output logic [31:0] import_arg3_o,

    // Debug memory read interface
    input  logic        dbg_mem_rd_en,
    input  logic [31:0] dbg_mem_rd_addr,
    output logic [31:0] dbg_mem_rd_data
);

    // CPU -> Memory interface
    logic        mem_rd_en;
    logic [31:0] mem_rd_addr;
    mem_op_t     mem_rd_op;
    logic        mem_wr_en;
    logic [31:0] mem_wr_addr;
    mem_op_t     mem_wr_op;
    logic [63:0] mem_wr_data;
    logic        mem_grow_en;
    logic [31:0] mem_grow_pages;

    // Memory -> CPU interface
    logic [63:0] mem_rd_data;
    logic        mem_rd_valid;
    logic        mem_wr_valid;
    logic [31:0] mem_current_pages;
    logic [31:0] mem_grow_result;
    trap_t       mem_trap;

    // CPU instance
    wasm_cpu #(
        .CODE_SIZE(CODE_SIZE),
        .STACK_SIZE(STACK_SIZE),
        .MEM_PAGES(MEM_PAGES)
    ) cpu (
        .clk(clk),
        .rst_n(rst_n),
        .start(start),
        .entry_func(entry_func),
        .halted(halted),
        .trapped(trapped),
        .trap_code(trap_code),
        .code_wr_en(code_wr_en),
        .code_wr_addr(code_wr_addr),
        .code_wr_data(code_wr_data),
        .func_wr_en(func_wr_en),
        .func_wr_idx(func_wr_idx),
        .func_wr_data(func_wr_data),
        .mem_init_en(mem_init_en),
        .mem_init_pages(mem_init_pages),
        .mem_init_max_pages(mem_init_max_pages),
        .mem_data_wr_en(mem_data_wr_en),
        .mem_data_wr_addr(mem_data_wr_addr),
        .mem_data_wr_data(mem_data_wr_data),
        .stack_init_en(stack_init_en),
        .stack_init_data(stack_init_data),
        .stack_reset_en(stack_reset_en),
        .local_init_wr_en(local_init_wr_en),
        .local_init_wr_base(local_init_wr_base),
        .local_init_wr_idx(local_init_wr_idx),
        .local_init_wr_data(local_init_wr_data),
        .global_init_en(global_init_en),
        .global_init_idx(global_init_idx),
        .global_init_data(global_init_data),
        .elem_init_en(elem_init_en),
        .elem_init_table_idx(elem_init_table_idx),
        .elem_init_idx(elem_init_idx),
        .elem_init_func_idx(elem_init_func_idx),
        .type_init_en(type_init_en),
        .type_init_idx(type_init_idx),
        .type_init_param_count(type_init_param_count),
        .type_init_result_count(type_init_result_count),
        .type_init_param_types(type_init_param_types),
        .type_init_result_types(type_init_result_types),
        .result_valid(result_valid),
        .result_value(result_value),
        .result_count(result_count),
        .result_values(result_values),
        .dbg_pc(dbg_pc),
        .dbg_state(dbg_state),
        .dbg_stack_ptr(dbg_stack_ptr),
        .dbg_saved_next_pc(dbg_saved_next_pc),
        .dbg_decode_next_pc(dbg_decode_next_pc),
        .dbg_instr_len(dbg_instr_len),
        .ext_halt_i(ext_halt_i),
        .ext_resume_i(ext_resume_i),
        .ext_resume_pc_i(ext_resume_pc_i),
        .ext_resume_val_i(ext_resume_val_i),
        .ext_halted_o(ext_halted_o),
        .import_id_o(import_id_o),
        .import_arg0_o(import_arg0_o),
        .import_arg1_o(import_arg1_o),
        .import_arg2_o(import_arg2_o),
        .import_arg3_o(import_arg3_o),
        .dbg_mem_rd_en(dbg_mem_rd_en),
        .dbg_mem_rd_addr(dbg_mem_rd_addr),
        .dbg_mem_rd_data(dbg_mem_rd_data),
        // Memory interface
        .mem_rd_en_o(mem_rd_en),
        .mem_rd_addr_o(mem_rd_addr),
        .mem_rd_op_o(mem_rd_op),
        .mem_wr_en_o(mem_wr_en),
        .mem_wr_addr_o(mem_wr_addr),
        .mem_wr_op_o(mem_wr_op),
        .mem_wr_data_o(mem_wr_data),
        .mem_grow_en_o(mem_grow_en),
        .mem_grow_pages_o(mem_grow_pages),
        .mem_rd_data_i(mem_rd_data),
        .mem_rd_valid_i(mem_rd_valid),
        .mem_wr_valid_i(mem_wr_valid),
        .mem_current_pages_i(mem_current_pages),
        .mem_grow_result_i(mem_grow_result),
        .mem_trap_i(mem_trap)
    );

    // Memory instance
    wasm_memory #(.MAX_PAGES(MEM_PAGES)) memory (
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

endmodule
