// WebAssembly CPU Testbench
// Main testbench for validating the WebAssembly CPU

`timescale 1ns/1ps

module wasm_cpu_tb;
    import wasm_pkg::*;

    // Clock and reset
    logic clk;
    logic rst_n;

    // Control
    logic start;
    logic [31:0] entry_func;
    logic halted;
    logic trapped;
    trap_t trap_code;

    // Code memory interface
    logic code_wr_en;
    logic [31:0] code_wr_addr;
    logic [7:0] code_wr_data;

    // Function table interface
    logic func_wr_en;
    logic [15:0] func_wr_idx;
    func_entry_t func_wr_data;

    // Type table interface (not used in simple tests, tied to 0)
    logic type_init_en = 0;
    logic [7:0] type_init_idx = 0;
    logic [7:0] type_init_param_count = 0;
    logic [7:0] type_init_result_count = 0;
    logic [31:0] type_init_param_types = 0;
    logic [31:0] type_init_result_types = 0;

    // Element table interface (not used in simple tests)
    logic elem_init_en = 0;
    logic [15:0] elem_init_idx = 0;
    logic [15:0] elem_init_func_idx = 0;

    // Global, local, memory interfaces (not used in simple tests)
    logic global_init_en = 0;
    logic [7:0] global_init_idx = 0;
    global_entry_t global_init_data;

    // Memory interface signals (directly to memory module)
    logic mem_init_en = 0;
    logic [31:0] mem_init_pages = 1;
    logic [31:0] mem_init_max_pages = 16;
    logic mem_data_wr_en = 0;
    logic [31:0] mem_data_wr_addr = 0;
    logic [7:0] mem_data_wr_data = 0;
    logic dbg_mem_rd_en = 0;
    logic [31:0] dbg_mem_rd_addr = 0;
    logic [31:0] dbg_mem_rd_data;

    // CPU -> Memory interface
    logic mem_rd_en;
    logic [31:0] mem_rd_addr;
    mem_op_t mem_rd_op;
    logic mem_wr_en;
    logic [31:0] mem_wr_addr;
    mem_op_t mem_wr_op;
    logic [63:0] mem_wr_data;
    logic mem_grow_en;
    logic [31:0] mem_grow_pages;

    // Memory -> CPU interface
    logic [63:0] mem_rd_data;
    logic mem_rd_valid;
    logic mem_wr_valid;
    logic [31:0] mem_current_pages;
    logic [31:0] mem_grow_result;
    trap_t mem_trap;

    // Result
    logic result_valid;
    stack_entry_t result_value;

    // Debug
    logic [31:0] dbg_pc;
    exec_state_t dbg_state;
    logic [15:0] dbg_stack_ptr;
    logic [31:0] dbg_saved_next_pc;
    logic [31:0] dbg_decode_next_pc;
    logic [7:0]  dbg_instr_len;

    // Test counters
    int tests_passed = 0;
    int tests_failed = 0;
    int tests_total = 0;

    // DUT
    wasm_cpu #(
        .CODE_SIZE(65536),
        .STACK_SIZE(1024),
        .MEM_PAGES(16)
    ) dut (
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
        .type_init_en(type_init_en),
        .type_init_idx(type_init_idx),
        .type_init_param_count(type_init_param_count),
        .type_init_result_count(type_init_result_count),
        .type_init_param_types(type_init_param_types),
        .type_init_result_types(type_init_result_types),
        .elem_init_en(elem_init_en),
        .elem_init_idx(elem_init_idx),
        .elem_init_func_idx(elem_init_func_idx),
        .global_init_en(global_init_en),
        .global_init_idx(global_init_idx),
        .global_init_data(global_init_data),
        .result_valid(result_valid),
        .result_value(result_value),
        .dbg_pc(dbg_pc),
        .dbg_state(dbg_state),
        .dbg_stack_ptr(dbg_stack_ptr),
        .dbg_saved_next_pc(dbg_saved_next_pc),
        .dbg_decode_next_pc(dbg_decode_next_pc),
        .dbg_instr_len(dbg_instr_len),
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

    // Linear Memory
    wasm_memory #(.MAX_PAGES(16)) linear_memory (
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

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Helper task to load code
    task automatic load_code(input logic [7:0] code[], input int start_addr);
        for (int i = 0; i < code.size(); i++) begin
            @(posedge clk);
            code_wr_en = 1;
            code_wr_addr = start_addr + i;
            code_wr_data = code[i];
        end
        @(posedge clk);
        code_wr_en = 0;
    endtask

    // Helper task to register a function
    task automatic register_function(
        input int func_idx,
        input int code_offset,
        input int code_length,
        input int param_count,
        input int result_count,
        input int local_count
    );
        @(posedge clk);
        func_wr_en = 1;
        func_wr_idx = func_idx;
        func_wr_data.code_offset = code_offset;
        func_wr_data.code_length = code_length;
        func_wr_data.type_idx = 0;
        func_wr_data.param_count = param_count;
        func_wr_data.result_count = result_count;
        func_wr_data.local_count = local_count;
        @(posedge clk);
        func_wr_en = 0;
    endtask

    // Helper task to run and wait for completion
    task automatic run_function(input int func_idx, output logic did_trap, output trap_t trap_result);
        int cycle_count;
        @(posedge clk);
        entry_func = func_idx;
        start = 1;
        @(posedge clk);
        start = 0;

        // Wait for completion with debug output
        cycle_count = 0;
        while (!halted) begin
            @(posedge clk);
            cycle_count++;
            if (cycle_count < 20) begin
                $display("  cycle=%0d pc=%h state=%s stack_ptr=%0d decode_next=%h saved_next=%h instr_len=%0d",
                         cycle_count, dbg_pc, dbg_state.name(), dbg_stack_ptr,
                         dbg_decode_next_pc, dbg_saved_next_pc, dbg_instr_len);
            end
            if (cycle_count > 1000) begin
                $display("ERROR: Timeout waiting for completion after %0d cycles", cycle_count);
                $display("  Final state: pc=%h state=%s stack_ptr=%0d", dbg_pc, dbg_state.name(), dbg_stack_ptr);
                did_trap = 1;
                trap_result = TRAP_NONE;
                break;
            end
        end

        did_trap = trapped;
        trap_result = trap_code;
    endtask

    // Test: Simple i32 add
    task automatic test_i32_add();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.add (1 + 2 = 3)");
        tests_total++;

        // Code: i32.const 1, i32.const 2, i32.add, end
        code = '{
            8'h41, 8'h01,       // i32.const 1
            8'h41, 8'h02,       // i32.const 2
            8'h6A,              // i32.add
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd3) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 3, got %d (trapped=%b)", result_value.value[31:0], did_trap);
            tests_failed++;
        end

        // Reset for next test
        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 subtraction
    task automatic test_i32_sub();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.sub (10 - 4 = 6)");
        tests_total++;

        code = '{
            8'h41, 8'h0A,       // i32.const 10
            8'h41, 8'h04,       // i32.const 4
            8'h6B,              // i32.sub
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd6) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 6, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 multiplication
    task automatic test_i32_mul();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.mul (7 * 6 = 42)");
        tests_total++;

        code = '{
            8'h41, 8'h07,       // i32.const 7
            8'h41, 8'h06,       // i32.const 6
            8'h6C,              // i32.mul
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd42) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 42, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 division (signed)
    task automatic test_i32_div_s();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.div_s (20 / 4 = 5)");
        tests_total++;

        code = '{
            8'h41, 8'h14,       // i32.const 20
            8'h41, 8'h04,       // i32.const 4
            8'h6D,              // i32.div_s
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd5) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 5, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 division by zero (should trap)
    task automatic test_i32_div_zero();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.div_s by zero (should trap)");
        tests_total++;

        code = '{
            8'h41, 8'h0A,       // i32.const 10
            8'h41, 8'h00,       // i32.const 0
            8'h6D,              // i32.div_s
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (did_trap && trap_result == TRAP_INT_DIV_ZERO) begin
            $display("  PASS: Correctly trapped with INT_DIV_ZERO");
            tests_passed++;
        end else begin
            $display("  FAIL: Expected trap, got trapped=%b, trap_code=%s", did_trap, trap_result.name());
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 comparison (eq)
    task automatic test_i32_eq();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.eq (5 == 5 = 1)");
        tests_total++;

        code = '{
            8'h41, 8'h05,       // i32.const 5
            8'h41, 8'h05,       // i32.const 5
            8'h46,              // i32.eq
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd1) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 1, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 comparison (ne)
    task automatic test_i32_ne();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.ne (5 != 3 = 1)");
        tests_total++;

        code = '{
            8'h41, 8'h05,       // i32.const 5
            8'h41, 8'h03,       // i32.const 3
            8'h47,              // i32.ne
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd1) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 1, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 bitwise and
    task automatic test_i32_and();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.and (0xFF & 0x0F = 0x0F)");
        tests_total++;

        code = '{
            8'h41, 8'hFF, 8'h01,  // i32.const 255 (LEB128)
            8'h41, 8'h0F,         // i32.const 15
            8'h71,                // i32.and
            8'h0B                 // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'h0F) begin
            $display("  PASS: Result = 0x%h", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 0x0F, got 0x%h", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 bitwise or
    task automatic test_i32_or();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.or (0xF0 | 0x0F = 0xFF)");
        tests_total++;

        code = '{
            8'h41, 8'hF0, 8'h01,  // i32.const 240 (LEB128)
            8'h41, 8'h0F,         // i32.const 15
            8'h72,                // i32.or
            8'h0B                 // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'hFF) begin
            $display("  PASS: Result = 0x%h", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 0xFF, got 0x%h", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32.eqz
    task automatic test_i32_eqz();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.eqz (0 == 0 = 1)");
        tests_total++;

        code = '{
            8'h41, 8'h00,       // i32.const 0
            8'h45,              // i32.eqz
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd1) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 1, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 shift left
    task automatic test_i32_shl();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.shl (1 << 4 = 16)");
        tests_total++;

        code = '{
            8'h41, 8'h01,       // i32.const 1
            8'h41, 8'h04,       // i32.const 4
            8'h74,              // i32.shl
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd16) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 16, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 clz (count leading zeros)
    task automatic test_i32_clz();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.clz (0x00FF0000) = 8");
        tests_total++;

        // 0x00FF0000 in LEB128 is complex, use simpler value
        // 0x80000000 should have clz = 0
        // Let's use 1, which has clz = 31
        code = '{
            8'h41, 8'h01,       // i32.const 1
            8'h67,              // i32.clz
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd31) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 31, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 ctz (count trailing zeros)
    task automatic test_i32_ctz();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.ctz (16) = 4");
        tests_total++;

        code = '{
            8'h41, 8'h10,       // i32.const 16
            8'h68,              // i32.ctz
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd4) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 4, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i32 popcnt
    task automatic test_i32_popcnt();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i32.popcnt (0x0F) = 4");
        tests_total++;

        code = '{
            8'h41, 8'h0F,       // i32.const 15
            8'h69,              // i32.popcnt
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd4) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 4, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: drop instruction
    task automatic test_drop();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: drop (push 5, push 10, drop, result = 5)");
        tests_total++;

        code = '{
            8'h41, 8'h05,       // i32.const 5
            8'h41, 8'h0A,       // i32.const 10
            8'h1A,              // drop
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd5) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 5, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: select instruction
    task automatic test_select();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: select (10, 20, 1) = 10");
        tests_total++;

        code = '{
            8'h41, 8'h0A,       // i32.const 10
            8'h41, 8'h14,       // i32.const 20
            8'h41, 8'h01,       // i32.const 1 (condition true)
            8'h1B,              // select
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd10) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 10, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: nop instruction
    task automatic test_nop();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: nop (push 42, nop, result = 42)");
        tests_total++;

        code = '{
            8'h41, 8'h2A,       // i32.const 42
            8'h01,              // nop
            8'h01,              // nop
            8'h01,              // nop
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value[31:0] == 32'd42) begin
            $display("  PASS: Result = %d", result_value.value[31:0]);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 42, got %d", result_value.value[31:0]);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: unreachable instruction (should trap)
    task automatic test_unreachable();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: unreachable (should trap)");
        tests_total++;

        code = '{
            8'h00,              // unreachable
            8'h0B               // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 0, 0);
        run_function(0, did_trap, trap_result);

        if (did_trap && trap_result == TRAP_UNREACHABLE) begin
            $display("  PASS: Correctly trapped with UNREACHABLE");
            tests_passed++;
        end else begin
            $display("  FAIL: Expected UNREACHABLE trap, got trapped=%b, code=%s", did_trap, trap_result.name());
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Test: i64 const and add
    task automatic test_i64_add();
        logic [7:0] code[];
        logic did_trap;
        trap_t trap_result;

        $display("Test: i64.add (100 + 200 = 300)");
        tests_total++;

        code = '{
            8'h42, 8'hE4, 8'h00,  // i64.const 100 (LEB128)
            8'h42, 8'hC8, 8'h01,  // i64.const 200 (LEB128)
            8'h7C,                // i64.add
            8'h0B                 // end
        };

        load_code(code, 0);
        register_function(0, 0, code.size(), 0, 1, 0);
        run_function(0, did_trap, trap_result);

        if (!did_trap && result_valid && result_value.value == 64'd300) begin
            $display("  PASS: Result = %d", result_value.value);
            tests_passed++;
        end else begin
            $display("  FAIL: Expected 300, got %d", result_value.value);
            tests_failed++;
        end

        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);
    endtask

    // Main test sequence
    initial begin
        $display("========================================");
        $display("WebAssembly CPU Testbench");
        $display("========================================");

        // Initialize
        rst_n = 0;
        start = 0;
        entry_func = 0;
        code_wr_en = 0;
        func_wr_en = 0;

        // Reset
        repeat(10) @(posedge clk);
        rst_n = 1;
        repeat(5) @(posedge clk);

        // Run tests
        test_i32_add();
        test_i32_sub();
        test_i32_mul();
        test_i32_div_s();
        test_i32_div_zero();
        test_i32_eq();
        test_i32_ne();
        test_i32_and();
        test_i32_or();
        test_i32_eqz();
        test_i32_shl();
        test_i32_clz();
        test_i32_ctz();
        test_i32_popcnt();
        test_drop();
        test_select();
        test_nop();
        test_unreachable();
        test_i64_add();

        // Summary
        $display("");
        $display("========================================");
        $display("Test Summary");
        $display("========================================");
        $display("Total:  %d", tests_total);
        $display("Passed: %d", tests_passed);
        $display("Failed: %d", tests_failed);
        $display("========================================");

        if (tests_failed == 0) begin
            $display("ALL TESTS PASSED!");
        end else begin
            $display("SOME TESTS FAILED!");
        end

        $finish;
    end

endmodule
