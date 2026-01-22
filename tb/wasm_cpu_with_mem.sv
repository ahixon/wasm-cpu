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

    // Table metadata initialization interface
    input  logic        table_init_en,
    input  logic [1:0]  table_init_idx,
    input  logic [15:0] table_init_size,
    input  logic [15:0] table_init_max_size,
    input  logic [3:0]  table_init_type,
    input  logic [31:0] table_init_base,

    // Element table initialization interface
    input  logic        elem_init_en,
    input  logic [1:0]  elem_init_table_idx,
    input  logic [15:0] elem_init_idx,
    input  logic [31:0] elem_init_value,

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

    // Table grow trap information
    output logic [1:0]  table_grow_table_idx_o,
    output logic [31:0] table_grow_delta_o,

    // Debug memory read interface
    input  logic        dbg_mem_rd_en,
    input  logic [31:0] dbg_mem_rd_addr,
    output logic [31:0] dbg_mem_rd_data
);

    // CPU -> Memory interface (struct-based)
    mem_bus_req_t  mem_req;
    mem_bus_resp_t mem_resp;
    mem_mgmt_req_t mem_mgmt_req;
    mem_mgmt_resp_t mem_mgmt_resp;
    mem_op_t       mem_op;
    trap_t         mem_trap;

    // CPU's debug memory read output (unused, memory drives dbg_mem_rd_data directly)
    logic [31:0] cpu_dbg_mem_rd_data;

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
        .table_init_en(table_init_en),
        .table_init_idx(table_init_idx),
        .table_init_size(table_init_size),
        .table_init_max_size(table_init_max_size),
        .table_init_type(table_init_type),
        .table_init_base(table_init_base),
        .elem_init_en(elem_init_en),
        .elem_init_table_idx(elem_init_table_idx),
        .elem_init_idx(elem_init_idx),
        .elem_init_value(elem_init_value),
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
        .table_grow_table_idx_o(table_grow_table_idx_o),
        .table_grow_delta_o(table_grow_delta_o),
        .dbg_mem_rd_en(dbg_mem_rd_en),
        .dbg_mem_rd_addr(dbg_mem_rd_addr),
        .dbg_mem_rd_data(cpu_dbg_mem_rd_data),
        // Memory bus interface (struct-based)
        .mem_req_o(mem_req),
        .mem_resp_i(mem_resp),
        .mem_mgmt_req_o(mem_mgmt_req),
        .mem_mgmt_resp_i(mem_mgmt_resp),
        .mem_op_o(mem_op),
        .mem_trap_i(mem_trap)
    );

    // Memory instance
    wasm_memory #(.MAX_PAGES(MEM_PAGES)) memory (
        .clk(clk),
        .rst_n(rst_n),
        // Memory bus interface (struct-based)
        .mem_req_i(mem_req),
        .mem_resp_o(mem_resp),
        .mem_op_i(mem_op),
        .mem_mgmt_req_i(mem_mgmt_req),
        .mem_mgmt_resp_o(mem_mgmt_resp),
        // Data segment initialization
        .data_wr_en(mem_data_wr_en),
        .data_wr_addr(mem_data_wr_addr),
        .data_wr_data(mem_data_wr_data),
        // Status
        .trap(mem_trap),
        // Debug interface
        .dbg_rd_en(dbg_mem_rd_en),
        .dbg_rd_addr(dbg_mem_rd_addr),
        .dbg_rd_data(dbg_mem_rd_data)
    );

endmodule
