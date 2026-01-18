// WebAssembly Test Runner
// Loads a .wasm file via plusargs and runs multiple assertions
// Usage: ./Vwasm_runner +wasm=test.wasm +tests=testlist.txt
//    or: ./Vwasm_runner +wasm=test.wasm +expected=42 +func=0 [+trap] [+i64]
// Test list format (one per line): <func_idx> <expected_hex> [trap] [i64]

`timescale 1ns/1ps

module wasm_runner;
    import wasm_pkg::*;

    logic clk = 0;
    logic rst_n;
    logic start;
    logic [31:0] entry_func;
    logic halted, trapped;
    trap_t trap_code;
    logic code_wr_en;
    logic [31:0] code_wr_addr;
    logic [7:0] code_wr_data;
    logic func_wr_en;
    logic [15:0] func_wr_idx;
    func_entry_t func_wr_data;
    logic result_valid;
    stack_entry_t result_value;
    logic [31:0] dbg_pc;
    exec_state_t dbg_state;
    logic [15:0] dbg_stack_ptr;
    logic [31:0] dbg_saved_next_pc, dbg_decode_next_pc;
    logic [7:0] dbg_instr_len;
    logic mem_init_en;
    logic [31:0] mem_init_pages;
    logic mem_data_wr_en;
    logic [31:0] mem_data_wr_addr;
    logic [7:0] mem_data_wr_data;

    wasm_cpu #(.CODE_SIZE(65536), .STACK_SIZE(1024), .MEM_PAGES(16)) dut (.*);

    always #5 clk = ~clk;

    // Load WASM file and extract code
    logic [7:0] wasm_data [0:65535];
    int wasm_size;

    // Plus args
    string wasm_file;
    string tests_file;
    longint expected_value;
    int expect_trap;
    int is_i64;
    int func_idx;
    int use_testlist;

    // Test list storage
    // test_mode: 0=verify result, 1=expect trap, 2=run only (void function)
    int test_func_list [0:1023];
    longint test_expected_list [0:1023];
    int test_mode_list [0:1023];
    int test_i64_list [0:1023];
    int num_tests;

    // Function information extracted from WASM
    typedef struct {
        int code_offset;
        int code_length;
        int local_count;
        int param_count;
        int result_count;
    } func_info_t;

    func_info_t func_info [0:255];
    int num_functions;
    int total_code_size;

    // Read LEB128 unsigned integer
    function automatic int read_leb128_u(inout int pos);
        int result, shift;
        result = 0;
        shift = 0;
        while (pos < wasm_size) begin
            result = result | ((wasm_data[pos] & 8'h7F) << shift);
            if ((wasm_data[pos] & 8'h80) == 0) begin
                pos++;
                return result;
            end
            pos++;
            shift = shift + 7;
        end
        return result;
    endfunction

    // Read LEB128 signed integer
    function automatic longint read_leb128_s(inout int pos);
        longint result;
        int shift;
        logic [7:0] byte_val;
        result = 0;
        shift = 0;
        while (pos < wasm_size) begin
            byte_val = wasm_data[pos];
            result = result | ((byte_val & 8'h7F) << shift);
            pos++;
            shift = shift + 7;
            if ((byte_val & 8'h80) == 0) begin
                // Sign extend if needed
                if ((byte_val & 8'h40) != 0 && shift < 64)
                    result = result | (~64'b0 << shift);
                return result;
            end
        end
        return result;
    endfunction

    // Extract all functions from WASM
    task automatic extract_all_functions();
        int pos, section_id, section_size;
        int type_count, func_count, code_count;
        int i, j, body_size, local_count, local_decl_count;
        int param_counts [0:255];
        int result_counts [0:255];
        int type_indices [0:255];
        int code_start;

        num_functions = 0;
        total_code_size = 0;

        // Check magic and version
        if (wasm_data[0] != 8'h00 || wasm_data[1] != 8'h61 ||
            wasm_data[2] != 8'h73 || wasm_data[3] != 8'h6D) begin
            $display("Invalid WASM magic");
            return;
        end

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            case (section_id)
                1: begin  // Type section
                    type_count = read_leb128_u(pos);
                    for (i = 0; i < type_count; i++) begin
                        pos++;  // Skip 0x60 (func type marker)
                        param_counts[i] = read_leb128_u(pos);
                        for (j = 0; j < param_counts[i]; j++)
                            pos++;  // Skip param types
                        result_counts[i] = read_leb128_u(pos);
                        for (j = 0; j < result_counts[i]; j++)
                            pos++;  // Skip result types
                    end
                end

                3: begin  // Function section
                    func_count = read_leb128_u(pos);
                    for (i = 0; i < func_count; i++) begin
                        type_indices[i] = read_leb128_u(pos);
                    end
                    num_functions = func_count;
                end

                10: begin  // Code section
                    int body_start_pos, local_decl_cnt, lcnt;
                    code_count = read_leb128_u(pos);
                    code_start = 0;
                    for (i = 0; i < code_count; i++) begin
                        body_size = read_leb128_u(pos);
                        body_start_pos = pos;

                        // Read local declarations
                        local_decl_cnt = read_leb128_u(pos);
                        lcnt = 0;
                        for (j = 0; j < local_decl_cnt; j++) begin
                            lcnt = lcnt + read_leb128_u(pos);
                            pos++;  // Skip type
                        end
                        local_count = lcnt;

                        // Store function info
                        func_info[i].code_offset = code_start + (pos - body_start_pos);
                        func_info[i].code_length = body_size - (pos - body_start_pos);
                        func_info[i].local_count = local_count;
                        func_info[i].param_count = param_counts[type_indices[i]];
                        func_info[i].result_count = result_counts[type_indices[i]];

                        // Skip to end of body
                        pos = body_start_pos + body_size;
                        code_start = code_start + body_size;
                    end
                    total_code_size = code_start;
                end

                default: begin
                    pos = pos + section_size;
                end
            endcase
        end
    endtask

    // Load all code into code memory
    task automatic load_all_code();
        int pos, section_id, section_size;
        int code_count, body_size;
        int code_addr;
        int i;

        code_addr = 0;
        pos = 8;

        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 10) begin  // Code section
                code_count = read_leb128_u(pos);
                for (i = 0; i < code_count; i++) begin
                    body_size = read_leb128_u(pos);
                    // Copy entire body (including locals prefix) to code memory
                    for (int j = 0; j < body_size; j++) begin
                        @(posedge clk);
                        code_wr_en = 1;
                        code_wr_addr = code_addr;
                        code_wr_data = wasm_data[pos + j];
                        code_addr++;
                    end
                    pos = pos + body_size;
                end
                @(posedge clk);
                code_wr_en = 0;
                return;
            end else begin
                pos = pos + section_size;
            end
        end
    endtask

    // Register all functions from WASM with correct offsets
    task automatic register_functions_from_wasm();
        int pos, section_id, section_size;
        int code_count, body_size, local_decl_count;
        int code_offset, body_start, code_start_in_body, actual_code_len;
        int i, j, dummy;

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 10) begin  // Code section
                code_count = read_leb128_u(pos);
                code_offset = 0;

                for (i = 0; i < code_count; i++) begin
                    body_size = read_leb128_u(pos);
                    body_start = pos;

                    // Read local declarations to find code start
                    local_decl_count = read_leb128_u(pos);
                    for (j = 0; j < local_decl_count; j++) begin
                        dummy = read_leb128_u(pos);  // count
                        pos++;  // type
                    end

                    // Now pos points to the actual code
                    code_start_in_body = pos - body_start;
                    actual_code_len = body_size - code_start_in_body;

                    @(posedge clk);
                    func_wr_en = 1;
                    func_wr_idx = i;
                    func_wr_data.code_offset = code_offset + code_start_in_body;
                    func_wr_data.code_length = actual_code_len;
                    func_wr_data.type_idx = 0;
                    func_wr_data.param_count = func_info[i].param_count;
                    func_wr_data.result_count = func_info[i].result_count;
                    func_wr_data.local_count = func_info[i].local_count;

                    pos = body_start + body_size;
                    code_offset = code_offset + body_size;
                end
                @(posedge clk);
                func_wr_en = 0;
                return;
            end else begin
                pos = pos + section_size;
            end
        end
    endtask

    // Extract initial memory size from WASM memory section
    function automatic int extract_memory_size();
        int pos, section_id, section_size, mem_count, flags, min_pages;

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 5) begin  // Memory section
                mem_count = read_leb128_u(pos);
                if (mem_count > 0) begin
                    flags = wasm_data[pos];
                    pos++;
                    min_pages = read_leb128_u(pos);
                    return min_pages;
                end
                return 0;
            end else begin
                pos = pos + section_size;
            end
        end
        return 1;  // Default
    endfunction

    // Data segment storage
    logic [7:0] data_bytes [0:65535];
    int data_offsets [0:63];
    int data_lengths [0:63];
    int num_data_segments;

    // Extract data segments from WASM data section
    task automatic extract_data_segments();
        int pos, section_id, section_size, seg_count, flags, offset, data_len;
        int data_pos;

        num_data_segments = 0;
        data_pos = 0;

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 11) begin  // Data section
                seg_count = read_leb128_u(pos);

                for (int seg = 0; seg < seg_count; seg++) begin
                    flags = wasm_data[pos];
                    pos++;

                    if (flags == 0) begin  // Active segment
                        if (wasm_data[pos] == 8'h41) begin  // i32.const
                            pos++;
                            offset = read_leb128_s(pos);
                            if (wasm_data[pos] == 8'h0B) pos++;  // end

                            data_len = read_leb128_u(pos);

                            data_offsets[num_data_segments] = offset;
                            data_lengths[num_data_segments] = data_len;

                            for (int i = 0; i < data_len; i++) begin
                                data_bytes[data_pos + i] = wasm_data[pos + i];
                            end
                            pos = pos + data_len;
                            data_pos = data_pos + data_len;
                            num_data_segments++;
                        end
                    end
                end
                return;
            end else begin
                pos = pos + section_size;
            end
        end
    endtask

    // Load data segments into memory
    task automatic load_data_segments();
        int data_pos;
        data_pos = 0;
        for (int seg = 0; seg < num_data_segments; seg++) begin
            for (int i = 0; i < data_lengths[seg]; i++) begin
                @(posedge clk);
                mem_data_wr_en = 1;
                mem_data_wr_addr = data_offsets[seg] + i;
                mem_data_wr_data = data_bytes[data_pos + i];
            end
            data_pos = data_pos + data_lengths[seg];
        end
        @(posedge clk);
        mem_data_wr_en = 0;
    endtask

    // Load code for single-function mode (legacy compatibility)
    function automatic int extract_code(output logic [7:0] code[], output int code_len);
        int pos, section_id, section_size, func_count, body_size, local_count;
        int body_start;

        if (wasm_data[0] != 8'h00 || wasm_data[1] != 8'h61 ||
            wasm_data[2] != 8'h73 || wasm_data[3] != 8'h6D) begin
            $display("Invalid WASM magic");
            return 0;
        end
        if (wasm_data[4] != 8'h01) begin
            $display("Invalid WASM version");
            return 0;
        end

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 10) begin  // Code section
                func_count = read_leb128_u(pos);
                body_size = read_leb128_u(pos);
                body_start = pos;
                local_count = read_leb128_u(pos);

                for (int i = 0; i < local_count; i++) begin
                    int dummy;
                    dummy = read_leb128_u(pos);  // count
                    pos++;  // type
                end

                code_len = body_start + body_size - pos;
                code = new[code_len];
                for (int i = 0; i < code_len; i++) begin
                    code[i] = wasm_data[pos + i];
                end
                return 1;
            end else begin
                pos = pos + section_size;
            end
        end
        return 0;
    endfunction

    // Parse test list file
    // Format: <func_idx> <expected_hex> <test_mode> <is_i64>
    // test_mode: 0=verify result, 1=expect trap, 2=run only (void function)
    task automatic parse_testlist(input string filename);
        int fd;
        string line;
        int func_id;
        longint expected;
        int test_mode, is_64;

        num_tests = 0;
        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("Cannot open test list file: %s", filename);
            return;
        end

        while (!$feof(fd)) begin
            int n;
            n = $fscanf(fd, "%d %h %d %d\n", func_id, expected, test_mode, is_64);
            if (n >= 2) begin
                test_func_list[num_tests] = func_id;
                test_expected_list[num_tests] = expected;
                test_mode_list[num_tests] = (n >= 3) ? test_mode : 0;
                test_i64_list[num_tests] = (n >= 4) ? is_64 : 0;
                num_tests++;
            end
        end
        $fclose(fd);
    endtask

    // Run a single test invocation
    // test_mode: 0=verify result, 1=expect trap, 2=run only (void function)
    task automatic run_invocation(
        input int func_id,
        input longint expected,
        input int test_mode,
        input int is_64,
        output int passed
    );
        int cycles;

        passed = 0;

        @(posedge clk);
        entry_func = func_id;
        start = 1;
        @(posedge clk);
        start = 0;

        // Wait for halted to go low (CPU has started)
        @(posedge clk);

        cycles = 0;
        while (!halted && cycles < 100000) begin
            @(posedge clk);
            cycles++;
        end

        case (test_mode)
            0: begin  // Normal test - verify result
                if (trapped) begin
                    passed = 0;
                end else if (is_64) begin
                    passed = (result_value.value == expected);
                end else begin
                    passed = (result_value.value[31:0] == expected[31:0]);
                end
            end
            1: begin  // Expect trap
                passed = trapped ? 1 : 0;
            end
            2: begin  // Run only (void function) - always pass if no unexpected trap
                passed = trapped ? 0 : 1;
            end
            default: begin
                passed = 0;
            end
        endcase
    endtask

    initial begin
        logic [7:0] code[];
        int code_len;
        int fd;
        int cycles;
        int init_mem_pages;
        int passed, total_passed, total_failed;
        int test_passed;

        rst_n = 0;
        start = 0;
        code_wr_en = 0;
        func_wr_en = 0;
        entry_func = 0;
        mem_init_en = 0;
        mem_init_pages = 0;
        mem_data_wr_en = 0;
        mem_data_wr_addr = 0;
        mem_data_wr_data = 0;

        // Get plusargs
        if (!$value$plusargs("wasm=%s", wasm_file)) begin
            $display("Usage: +wasm=<file.wasm> +tests=<testlist.txt>");
            $display("   or: +wasm=<file.wasm> +expected=<value> [+func=<idx>] [+trap] [+i64]");
            $finish;
        end

        // Check for test list mode vs single test mode
        use_testlist = $value$plusargs("tests=%s", tests_file);

        if (!use_testlist) begin
            // Legacy single test mode
            expect_trap = $test$plusargs("trap");
            is_i64 = $test$plusargs("i64");
            if (!$value$plusargs("func=%d", func_idx))
                func_idx = 0;

            if (!expect_trap) begin
                if (!$value$plusargs("expected=%h", expected_value)) begin
                    $display("Must specify +expected=<hex_value> or +trap");
                    $finish;
                end
            end
        end

        // Load WASM file
        fd = $fopen(wasm_file, "rb");
        if (fd == 0) begin
            $display("Cannot open %s", wasm_file);
            $finish;
        end

        wasm_size = 0;
        while (!$feof(fd)) begin
            wasm_data[wasm_size] = $fgetc(fd);
            wasm_size++;
        end
        $fclose(fd);
        wasm_size--;  // Remove EOF

        // Extract memory size
        init_mem_pages = extract_memory_size();

        // Reset
        @(posedge clk);
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);

        // Initialize memory size
        @(posedge clk);
        mem_init_en = 1;
        mem_init_pages = init_mem_pages;
        @(posedge clk);
        mem_init_en = 0;
        mem_init_pages = 0;
        @(posedge clk);

        // Extract and load data segments
        extract_data_segments();
        load_data_segments();

        if (use_testlist) begin
            // Multi-test mode: extract all functions
            extract_all_functions();

            // Load all code
            load_all_code();

            // Register all functions with proper offsets
            register_functions_from_wasm();

            // Parse test list
            parse_testlist(tests_file);

            if (num_tests == 0) begin
                $display("No tests found in %s", tests_file);
                $finish;
            end

            // Run all tests
            total_passed = 0;
            total_failed = 0;

            for (int t = 0; t < num_tests; t++) begin
                run_invocation(
                    test_func_list[t],
                    test_expected_list[t],
                    test_mode_list[t],
                    test_i64_list[t],
                    test_passed
                );

                if (test_passed) begin
                    total_passed++;
                end else begin
                    total_failed++;
                    if (test_mode_list[t] == 1) begin
                        $display("FAIL: test %0d func %0d (expected trap, got %0d)",
                            t, test_func_list[t], result_value.value);
                    end else if (test_mode_list[t] == 2) begin
                        $display("FAIL: test %0d func %0d (void func trapped unexpectedly)",
                            t, test_func_list[t]);
                    end else if (trapped) begin
                        $display("FAIL: test %0d func %0d (unexpected trap)",
                            t, test_func_list[t]);
                    end else begin
                        $display("FAIL: test %0d func %0d expected %0h, got %0h",
                            t, test_func_list[t], test_expected_list[t],
                            test_i64_list[t] ? result_value.value : result_value.value[31:0]);
                    end
                end
            end

            if (total_failed == 0) begin
                $display("PASS: %s (%0d tests)", wasm_file, total_passed);
            end else begin
                $display("FAIL: %s (%0d passed, %0d failed)", wasm_file, total_passed, total_failed);
            end

        end else begin
            // Legacy single-function mode
            if (!extract_code(code, code_len)) begin
                $display("FAIL: Cannot extract code from %s", wasm_file);
                $finish;
            end

            // Load code
            for (int i = 0; i < code_len; i++) begin
                @(posedge clk);
                code_wr_en = 1;
                code_wr_addr = i;
                code_wr_data = code[i];
            end
            @(posedge clk);
            code_wr_en = 0;

            // Register function
            @(posedge clk);
            func_wr_en = 1;
            func_wr_idx = 0;
            func_wr_data.code_offset = 0;
            func_wr_data.code_length = code_len;
            func_wr_data.type_idx = 0;
            func_wr_data.param_count = 0;
            func_wr_data.result_count = 1;
            func_wr_data.local_count = 0;
            @(posedge clk);
            func_wr_en = 0;

            // Run
            @(posedge clk);
            entry_func = func_idx;
            start = 1;
            @(posedge clk);
            start = 0;

            cycles = 0;
            while (!halted && cycles < 100000) begin
                @(posedge clk);
                cycles++;
            end

            // Check result
            if (expect_trap) begin
                if (trapped) begin
                    $display("PASS: %s (trapped as expected)", wasm_file);
                end else begin
                    $display("FAIL: %s (expected trap, got %0d)", wasm_file, result_value.value);
                end
            end else begin
                if (trapped) begin
                    $display("FAIL: %s (unexpected trap)", wasm_file);
                end else if (is_i64) begin
                    if (result_value.value == expected_value) begin
                        $display("PASS: %s = %0d", wasm_file, result_value.value);
                    end else begin
                        $display("FAIL: %s expected %0d, got %0d", wasm_file, expected_value, result_value.value);
                    end
                end else begin
                    if (result_value.value[31:0] == expected_value[31:0]) begin
                        $display("PASS: %s = %0d", wasm_file, result_value.value[31:0]);
                    end else begin
                        $display("FAIL: %s expected %0d, got %0d", wasm_file, expected_value[31:0], result_value.value[31:0]);
                    end
                end
            end
        end

        $finish;
    end

endmodule
