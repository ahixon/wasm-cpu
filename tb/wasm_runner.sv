// WebAssembly Test Runner
// Loads a .wasm file via plusargs and runs multiple assertions
// Usage: ./Vwasm_runner +wasm=test.wasm +tests=testlist.txt
//    or: ./Vwasm_runner +wasm=test.wasm +expected=42 +func=0 [+trap] [+i64]
// Test list format (one per line):
//   <func_idx> <test_mode> <num_args> [<arg_type> <arg_hex>]... <num_results> [<result_type> <result_hex>]...
// test_mode: 0=verify result, 1=expect trap, 2=run only (void function)
// arg_type/result_type: 0=i32, 1=i64, 2=f32, 3=f64

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
    logic [7:0] result_count;
    stack_entry_t result_values [0:15];
    logic [31:0] dbg_pc;
    exec_state_t dbg_state;
    logic [15:0] dbg_stack_ptr;
    logic [31:0] dbg_saved_next_pc, dbg_decode_next_pc;
    logic [7:0] dbg_instr_len;
    logic mem_init_en;
    logic [31:0] mem_init_pages;
    logic [31:0] mem_init_max_pages;
    logic mem_data_wr_en;
    logic [31:0] mem_data_wr_addr;
    logic [7:0] mem_data_wr_data;
    logic stack_init_en;
    stack_entry_t stack_init_data;
    logic stack_reset_en;
    logic local_init_wr_en;
    logic [15:0] local_init_wr_base;
    logic [7:0] local_init_wr_idx;
    stack_entry_t local_init_wr_data;
    logic global_init_en;
    logic [7:0] global_init_idx;
    global_entry_t global_init_data;
    logic table_init_en;
    logic [1:0] table_init_idx;
    logic [15:0] table_init_size;
    logic [15:0] table_init_max_size;
    logic [3:0] table_init_type;
    logic [31:0] table_init_base;  // Base address for table in linear memory
    logic elem_init_en;
    logic [1:0] elem_init_table_idx;
    logic [15:0] elem_init_idx;
    logic [31:0] elem_init_value;

    // Element segment metadata initialization interface
    logic        elem_seg_init_en;
    logic [3:0]  elem_seg_init_idx;
    logic [31:0] elem_seg_init_base;
    logic [15:0] elem_seg_init_size;
    logic [3:0]  elem_seg_init_type;
    logic        elem_seg_init_dropped;

    // Data segment metadata initialization interface
    logic        data_seg_init_en;
    logic [3:0]  data_seg_init_idx;
    logic [31:0] data_seg_init_base;
    logic [31:0] data_seg_init_size;
    logic        data_seg_init_dropped;

    // Table base address configuration
    // Tables are stored in linear memory at these base addresses
    // Use addresses within the first 64KB page to avoid bounds issues
    // Tables are placed at 32KB offset (0x8000), giving 8KB per table (2048 entries max)
    // This ensures all 4 tables fit within 32KB (0x8000-0xFFFF)
    localparam logic [31:0] TB_TABLE_BASE = 32'h0000_8000;  // 32KB offset
    localparam int TB_TABLE_STRIDE = 32'h0000_2000;         // 8KB per table (2048 entries max)

    // Element segment base address configuration
    // Element segments are stored after tables: 0x10000 + (seg_idx * 0x400)
    // Each segment has up to 256 elements (1KB), supporting 16 segments
    localparam logic [31:0] TB_ELEM_SEG_BASE = 32'h0001_0000;  // 64KB offset
    localparam int TB_ELEM_SEG_STRIDE = 32'h0000_0400;          // 1KB per segment (256 entries max)

    // Data segment base address configuration (for passive segments used by memory.init)
    // Passive data segments are stored at: 0x100000 + (seg_idx * 0x1000)
    // This is in the "internal region" (1MB+) which bypasses wasm bounds checking
    // Each segment has up to 4KB of data, supporting 16 segments (64KB total)
    localparam logic [31:0] TB_DATA_SEG_BASE = 32'h0010_0000;  // 1MB offset
    localparam int TB_DATA_SEG_STRIDE = 32'h0000_1000;          // 4KB per segment

    logic type_init_en;
    logic [7:0] type_init_idx;
    logic [7:0] type_init_param_count;
    logic [7:0] type_init_result_count;
    logic [31:0] type_init_param_types;
    logic [31:0] type_init_result_types;

    // External halt/resume interface (for SoC integration, unused in standalone tests)
    logic ext_halt_i = 0;
    logic ext_resume_i = 0;
    logic [31:0] ext_resume_pc_i = 0;
    logic [31:0] ext_resume_val_i = 0;
    logic ext_halted_o;

    // Import trap information
    logic [15:0] import_id_o;
    logic [31:0] import_arg0_o;
    logic [31:0] import_arg1_o;
    logic [31:0] import_arg2_o;
    logic [31:0] import_arg3_o;

    // Table grow trap information
    logic [1:0]  table_grow_table_idx_o;
    logic [31:0] table_grow_delta_o;

    // Debug memory read interface
    logic dbg_mem_rd_en = 0;
    logic [31:0] dbg_mem_rd_addr = 0;
    logic [31:0] dbg_mem_rd_data;

    // CPU -> Memory interface (struct-based, names must match CPU ports for .* connection)
    mem_bus_req_t  mem_req_o;
    mem_bus_resp_t mem_resp_i;
    mem_mgmt_req_t mem_mgmt_req_o;
    mem_mgmt_resp_t mem_mgmt_resp_i;
    mem_op_t       mem_op_o;
    trap_t         mem_trap_i;

    wasm_cpu #(.CODE_SIZE(65536), .STACK_SIZE(1024), .MEM_PAGES(1024)) dut (.*);

    // Linear Memory
    wasm_memory #(.MAX_PAGES(1024)) linear_memory (
        .clk(clk),
        .rst_n(rst_n),
        // Memory bus interface (struct-based)
        .mem_req_i(mem_req_o),
        .mem_resp_o(mem_resp_i),
        .mem_op_i(mem_op_o),
        .mem_mgmt_req_i(mem_mgmt_req_o),
        .mem_mgmt_resp_o(mem_mgmt_resp_i),
        // Data segment initialization
        .data_wr_en(mem_data_wr_en),
        .data_wr_addr(mem_data_wr_addr),
        .data_wr_data(mem_data_wr_data),
        // Status
        .trap(mem_trap_i),
        // Debug interface
        .dbg_rd_en(dbg_mem_rd_en),
        .dbg_rd_addr(dbg_mem_rd_addr),
        .dbg_rd_data(dbg_mem_rd_data)
    );

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
    int test_mode_list [0:1023];
    int num_tests;

    // Result storage for tests (supports multi-value returns)
    // Max 16 results per test, 1024 tests
    int test_num_results [0:1023];
    int test_result_types [0:1023][0:15];     // 0=i32, 1=i64, 2=f32, 3=f64
    longint test_result_values [0:1023][0:15];

    // Argument storage for tests
    // Max 32 arguments per test, 1024 tests
    int test_num_args [0:1023];
    int test_arg_types [0:1023][0:31];       // 0=i32, 1=i64, 2=f32, 3=f64
    longint test_arg_values [0:1023][0:31];

    // Function information extracted from WASM
    typedef struct {
        int code_offset;
        int code_length;
        int local_count;
        int param_count;
        int result_count;
        int type_idx;
    } func_info_t;

    func_info_t func_info [0:255];
    int num_functions;
    int total_code_size;

    // Type information extracted from WASM
    typedef struct {
        int param_count;
        int result_count;
        int param_types;   // Packed 4-bit valtypes, up to 8 params
        int result_types;  // Packed 4-bit valtypes, up to 8 results
    } type_info_t;

    type_info_t type_info [0:255];
    int num_types;

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
                    int packed_params, packed_results;
                    int valtype;
                    type_count = read_leb128_u(pos);
                    num_types = type_count;  // Store globally
                    for (i = 0; i < type_count; i++) begin
                        pos++;  // Skip 0x60 (func type marker)
                        param_counts[i] = read_leb128_u(pos);
                        packed_params = 0;
                        for (j = 0; j < param_counts[i] && j < 8; j++) begin
                            // Convert WASM valtype to our 4-bit encoding
                            // WASM: 0x7F=i32, 0x7E=i64, 0x7D=f32, 0x7C=f64, 0x70=funcref, 0x6F=externref
                            // Typed refs: 0x63=ref null t, 0x64=ref t (followed by heaptype LEB128)
                            // Ours: 0=i32, 1=i64, 2=f32, 3=f64, 5=funcref, 6=externref
                            valtype = wasm_data[pos];
                            case (valtype)
                                8'h7F: packed_params = packed_params | (0 << (j * 4));  // i32
                                8'h7E: packed_params = packed_params | (1 << (j * 4));  // i64
                                8'h7D: packed_params = packed_params | (2 << (j * 4));  // f32
                                8'h7C: packed_params = packed_params | (3 << (j * 4));  // f64
                                8'h70: packed_params = packed_params | (5 << (j * 4));  // funcref
                                8'h6F: packed_params = packed_params | (6 << (j * 4));  // externref
                                8'h63, 8'h64: begin
                                    // Typed reference: ref null t (0x63) or ref t (0x64)
                                    // Treat as funcref for now (could be externref depending on heaptype)
                                    packed_params = packed_params | (5 << (j * 4));
                                    pos++;  // Skip the valtype byte
                                    // Skip the heaptype LEB128
                                    void'(read_leb128_s(pos));
                                    continue;  // Don't increment pos again at end
                                end
                            endcase
                            pos++;
                        end
                        // Skip any remaining params beyond 8
                        for (j = 8; j < param_counts[i]; j++)
                            pos++;
                        result_counts[i] = read_leb128_u(pos);
                        packed_results = 0;
                        for (j = 0; j < result_counts[i] && j < 8; j++) begin
                            valtype = wasm_data[pos];
                            case (valtype)
                                8'h7F: packed_results = packed_results | (0 << (j * 4));  // i32
                                8'h7E: packed_results = packed_results | (1 << (j * 4));  // i64
                                8'h7D: packed_results = packed_results | (2 << (j * 4));  // f32
                                8'h7C: packed_results = packed_results | (3 << (j * 4));  // f64
                                8'h70: packed_results = packed_results | (5 << (j * 4));  // funcref
                                8'h6F: packed_results = packed_results | (6 << (j * 4));  // externref
                                8'h63, 8'h64: begin
                                    // Typed reference: ref null t (0x63) or ref t (0x64)
                                    packed_results = packed_results | (5 << (j * 4));
                                    pos++;  // Skip the valtype byte
                                    void'(read_leb128_s(pos));  // Skip the heaptype LEB128
                                    continue;
                                end
                            endcase
                            pos++;
                        end
                        // Skip any remaining results beyond 8
                        for (j = 8; j < result_counts[i]; j++)
                            pos++;
                        // Store in global type_info
                        type_info[i].param_count = param_counts[i];
                        type_info[i].result_count = result_counts[i];
                        type_info[i].param_types = packed_params;
                        type_info[i].result_types = packed_results;
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
                            int local_type;
                            lcnt = lcnt + read_leb128_u(pos);
                            local_type = wasm_data[pos];
                            pos++;  // Skip type byte
                            // Handle typed references (0x63 = ref null t, 0x64 = ref t)
                            if (local_type == 8'h63 || local_type == 8'h64) begin
                                void'(read_leb128_s(pos));  // Skip heaptype LEB128
                            end
                        end
                        local_count = lcnt;

                        // Store function info
                        func_info[i].code_offset = code_start + (pos - body_start_pos);
                        func_info[i].code_length = body_size - (pos - body_start_pos);
                        func_info[i].local_count = local_count;
                        func_info[i].param_count = param_counts[type_indices[i]];
                        func_info[i].result_count = result_counts[type_indices[i]];
                        func_info[i].type_idx = type_indices[i];

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
                        int local_type;
                        dummy = read_leb128_u(pos);  // count
                        local_type = wasm_data[pos];
                        pos++;  // type byte
                        // Handle typed references (0x63 = ref null t, 0x64 = ref t)
                        if (local_type == 8'h63 || local_type == 8'h64) begin
                            void'(read_leb128_s(pos));  // Skip heaptype LEB128
                        end
                    end

                    // Now pos points to the actual code
                    code_start_in_body = pos - body_start;
                    actual_code_len = body_size - code_start_in_body;

                    @(posedge clk);
                    func_wr_en = 1;
                    func_wr_idx = i;
                    func_wr_data.code_offset = code_offset + code_start_in_body;
                    func_wr_data.code_length = actual_code_len;
                    func_wr_data.type_idx = func_info[i].type_idx;
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

    // Extract initial memory size and max from WASM memory section
    task automatic extract_memory_info(output int min_pages, output int max_pages);
        int pos, section_id, section_size, mem_count, flags;

        min_pages = 1;  // Default
        max_pages = 0;  // 0 = no limit

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
                    // If bit 0 of flags is set, max_pages follows
                    if (flags & 1) begin
                        max_pages = read_leb128_u(pos);
                    end
                    return;
                end
                min_pages = 0;
                return;
            end else begin
                pos = pos + section_size;
            end
        end
    endtask

    // Data segment storage (for memory.init) - support up to 16 segments
    // Passive segment data is stored in memory starting at TB_DATA_SEG_BASE
    typedef struct {
        int offset;              // Destination offset in memory (for active segments)
        int length;              // Length of data in bytes
        int data_start;          // Start index in data_bytes array
        logic is_passive;        // 1 = passive (available for memory.init), 0 = active (dropped)
    } data_seg_info_t;
    data_seg_info_t data_segments [0:15];
    logic [7:0] data_bytes [0:65535];
    int data_bytes_pos;          // Current position in data_bytes array
    int num_data_segments;

    // Extract data segments from WASM data section
    task automatic extract_data_segments();
        int pos, section_id, section_size, seg_count, flags, offset, data_len;
        int seg_idx;

        num_data_segments = 0;
        data_bytes_pos = 0;

        // Initialize all segments as dropped
        for (int s = 0; s < 16; s++) begin
            data_segments[s].offset = 0;
            data_segments[s].length = 0;
            data_segments[s].data_start = 0;
            data_segments[s].is_passive = 0;
        end

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 11) begin  // Data section
                seg_count = read_leb128_u(pos);

                for (int seg = 0; seg < seg_count && seg < 16; seg++) begin
                    flags = wasm_data[pos];
                    pos++;
                    seg_idx = num_data_segments;

                    if (flags == 0) begin  // Active segment (memory 0, with offset)
                        if (wasm_data[pos] == 8'h41) begin  // i32.const
                            pos++;
                            offset = read_leb128_s(pos);
                            if (wasm_data[pos] == 8'h0B) pos++;  // end

                            data_len = read_leb128_u(pos);

                            data_segments[seg_idx].offset = offset;
                            data_segments[seg_idx].length = data_len;
                            data_segments[seg_idx].data_start = data_bytes_pos;
                            data_segments[seg_idx].is_passive = 0;  // Active = dropped after instantiation

                            for (int i = 0; i < data_len; i++) begin
                                data_bytes[data_bytes_pos + i] = wasm_data[pos + i];
                            end
                            pos = pos + data_len;
                            data_bytes_pos = data_bytes_pos + data_len;
                            num_data_segments++;
                        end
                    end else if (flags == 1) begin  // Passive segment
                        data_len = read_leb128_u(pos);

                        data_segments[seg_idx].offset = 0;  // No destination for passive
                        data_segments[seg_idx].length = data_len;
                        data_segments[seg_idx].data_start = data_bytes_pos;
                        data_segments[seg_idx].is_passive = 1;  // Passive = available for memory.init

                        for (int i = 0; i < data_len; i++) begin
                            data_bytes[data_bytes_pos + i] = wasm_data[pos + i];
                        end
                        pos = pos + data_len;
                        data_bytes_pos = data_bytes_pos + data_len;
                        num_data_segments++;
                    end else if (flags == 2) begin  // Active segment with explicit memory index
                        int mem_idx;
                        mem_idx = read_leb128_u(pos);  // memory index (should be 0)
                        if (wasm_data[pos] == 8'h41) begin  // i32.const
                            pos++;
                            offset = read_leb128_s(pos);
                            if (wasm_data[pos] == 8'h0B) pos++;  // end

                            data_len = read_leb128_u(pos);

                            data_segments[seg_idx].offset = offset;
                            data_segments[seg_idx].length = data_len;
                            data_segments[seg_idx].data_start = data_bytes_pos;
                            data_segments[seg_idx].is_passive = 0;  // Active = dropped

                            for (int i = 0; i < data_len; i++) begin
                                data_bytes[data_bytes_pos + i] = wasm_data[pos + i];
                            end
                            pos = pos + data_len;
                            data_bytes_pos = data_bytes_pos + data_len;
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
    // Active segments are loaded to their destination address
    // Passive segments are loaded to TB_DATA_SEG_BASE area for memory.init
    task automatic load_data_segments();
        for (int seg = 0; seg < num_data_segments; seg++) begin
            int base_addr;
            if (data_segments[seg].is_passive) begin
                // Passive segment: store at reserved area for memory.init
                base_addr = TB_DATA_SEG_BASE + (seg * TB_DATA_SEG_STRIDE);
            end else begin
                // Active segment: store at destination offset
                base_addr = data_segments[seg].offset;
            end

            for (int i = 0; i < data_segments[seg].length; i++) begin
                @(posedge clk);
                mem_data_wr_en = 1;
                mem_data_wr_addr = base_addr + i;
                mem_data_wr_data = data_bytes[data_segments[seg].data_start + i];
            end
        end
        @(posedge clk);
        mem_data_wr_en = 0;
    endtask

    // Load data segment metadata into CPU for memory.init/data.drop
    task automatic load_data_segment_metadata();
        for (int s = 0; s < num_data_segments; s++) begin
            @(posedge clk);
            data_seg_init_en = 1;
            data_seg_init_idx = s[3:0];
            if (data_segments[s].is_passive) begin
                // Passive: base points to reserved area, not dropped
                data_seg_init_base = TB_DATA_SEG_BASE + (s * TB_DATA_SEG_STRIDE);
                data_seg_init_dropped = 0;
            end else begin
                // Active: base doesn't matter (already loaded), marked as dropped
                data_seg_init_base = 0;
                data_seg_init_dropped = 1;
            end
            data_seg_init_size = data_segments[s].length;
        end
        @(posedge clk);
        data_seg_init_en = 0;
    endtask

    // Global variables storage
    global_entry_t global_entries [0:255];
    int num_globals;

    // Extract globals from WASM global section
    task automatic extract_globals();
        int pos, section_id, section_size, global_count;
        int valtype, mutability;
        longint init_val;
        int opcode;

        num_globals = 0;

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 6) begin  // Global section
                global_count = read_leb128_u(pos);

                for (int g = 0; g < global_count && g < 256; g++) begin
                    // Global type: valtype + mutability
                    valtype = wasm_data[pos];
                    pos++;
                    mutability = wasm_data[pos];
                    pos++;

                    // Init expression: opcode + value + end
                    opcode = wasm_data[pos];
                    pos++;

                    case (opcode)
                        8'h41: begin  // i32.const
                            init_val = read_leb128_s(pos);
                            global_entries[num_globals].vtype = TYPE_I32;
                        end
                        8'h42: begin  // i64.const
                            init_val = read_leb128_s(pos);
                            global_entries[num_globals].vtype = TYPE_I64;
                        end
                        8'h43: begin  // f32.const
                            init_val = {wasm_data[pos+3], wasm_data[pos+2], wasm_data[pos+1], wasm_data[pos]};
                            pos = pos + 4;
                            global_entries[num_globals].vtype = TYPE_F32;
                        end
                        8'h44: begin  // f64.const
                            init_val = {wasm_data[pos+7], wasm_data[pos+6], wasm_data[pos+5], wasm_data[pos+4],
                                        wasm_data[pos+3], wasm_data[pos+2], wasm_data[pos+1], wasm_data[pos]};
                            pos = pos + 8;
                            global_entries[num_globals].vtype = TYPE_F64;
                        end
                        8'hD0: begin  // ref.null heaptype
                            read_leb128_s(pos);  // skip heaptype
                            init_val = 64'hFFFFFFFF;  // REF_NULL_VALUE
                            // Use declared type from global type section
                            case (valtype)
                                8'h70: global_entries[num_globals].vtype = TYPE_FUNCREF;
                                8'h6F: global_entries[num_globals].vtype = TYPE_EXTERNREF;
                                default: global_entries[num_globals].vtype = TYPE_FUNCREF;
                            endcase
                        end
                        8'hD2: begin  // ref.func funcidx
                            init_val = read_leb128_u(pos);  // function index
                            global_entries[num_globals].vtype = TYPE_FUNCREF;
                        end
                        default: begin
                            init_val = 0;
                            global_entries[num_globals].vtype = TYPE_I32;
                        end
                    endcase

                    if (wasm_data[pos] == 8'h0B) pos++;  // end

                    global_entries[num_globals].value = init_val;
                    global_entries[num_globals].mutable_flag = (mutability == 1);
                    num_globals++;
                end
                return;
            end else begin
                pos = pos + section_size;
            end
        end
    endtask

    // Load globals into global storage
    task automatic load_globals();
        for (int g = 0; g < num_globals; g++) begin
            @(posedge clk);
            global_init_en = 1;
            global_init_idx = g[7:0];
            global_init_data = global_entries[g];
        end
        @(posedge clk);
        global_init_en = 0;
    endtask

    // Element table storage (for call_indirect) - support up to 4 tables
    int elem_entries [0:3][0:255];  // Function indices per table
    int declared_min_size [0:3];     // Declared minimum size from table section
    int num_elements [0:3];          // Number of elements to initialize (may exceed declared size)
    int max_elements [0:3];          // Max size of each table (0 = no limit)
    logic [7:0] table_types [0:3];   // Element types (0x70=funcref, 0x6F=externref)
    int current_table_size [0:3];    // Current runtime size of each table (for table.grow tracking)

    // Element segment storage (for table.init) - support up to 16 segments
    // Segment data is stored in memory starting at TB_ELEM_SEG_BASE
    typedef struct {
        int entries [0:255];         // Function indices in this segment
        int size;                    // Number of entries
        logic [7:0] elem_type;       // Element type (0x70=funcref, 0x6F=externref)
        logic is_passive;            // 1 = passive (available for table.init), 0 = active/declarative (dropped)
    } elem_seg_info_t;
    elem_seg_info_t elem_segments [0:15];
    int num_elem_segments;           // Total number of element segments in module

    // Extract table section from WASM (section 4) to get table sizes and types
    task automatic extract_tables();
        int pos, section_id, section_size, table_count;
        int elem_type, flags, min_size, max_size;

        // Initialize all tables with default values
        for (int t = 0; t < 4; t++) begin
            declared_min_size[t] = 0;
            num_elements[t] = 0;
            max_elements[t] = 0;  // 0 = no limit
            table_types[t] = 8'h70;  // Default to funcref
            current_table_size[t] = 0;  // Will be set from declared_min_size after load_table_metadata
        end

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 4) begin  // Table section
                table_count = read_leb128_u(pos);

                for (int t = 0; t < table_count && t < 4; t++) begin
                    // Parse element type
                    elem_type = wasm_data[pos];
                    pos++;

                    // Handle typed ref format: 0x63/0x64 followed by heaptype
                    if (elem_type == 8'h63 || elem_type == 8'h64) begin
                        // ref null heaptype or ref heaptype
                        int heaptype;
                        heaptype = read_leb128_s(pos);  // heaptype can be negative (abstract) or positive (typeidx)
                        // Map abstract heap types to element types
                        if (heaptype == -16 || heaptype == -13) begin  // func or nofunc
                            table_types[t] = 8'h70;  // funcref
                        end else if (heaptype == -17 || heaptype == -14) begin  // extern or noextern
                            table_types[t] = 8'h6F;  // externref
                        end else begin
                            // It's a type index - treat as funcref
                            table_types[t] = 8'h70;
                        end
                    end else begin
                        table_types[t] = elem_type[7:0];
                    end

                    // Parse limits
                    flags = wasm_data[pos];
                    pos++;
                    min_size = read_leb128_u(pos);
                    max_size = 0;  // 0 = no limit
                    if (flags & 1) begin
                        max_size = read_leb128_u(pos);
                    end

                    // Set table size to min_size and track max
                    declared_min_size[t] = min_size;
                    num_elements[t] = min_size;
                    max_elements[t] = max_size;
                end
                return;
            end else begin
                pos = pos + section_size;
            end
        end
    endtask

    // Extract element section from WASM (section 9)
    // Must be called AFTER extract_tables() to have proper table sizes
    // Stores both table entries (for active segments) and segment metadata (for table.init)
    task automatic extract_elements();
        int pos, section_id, section_size, elem_count;
        int flags, table_idx, offset_val, num_funcs;
        int opcode, elemtype;
        int seg_idx;  // Current segment index

        // Initialize all table entries to null
        for (int t = 0; t < 4; t++) begin
            for (int i = 0; i < 256; i++) begin
                elem_entries[t][i] = -1;  // -1 = null reference
            end
        end

        // Initialize all element segments
        num_elem_segments = 0;
        for (int s = 0; s < 16; s++) begin
            elem_segments[s].size = 0;
            elem_segments[s].elem_type = 8'h70;  // funcref default
            elem_segments[s].is_passive = 0;
            for (int i = 0; i < 256; i++) begin
                elem_segments[s].entries[i] = -1;
            end
        end

        pos = 8;
        while (pos < wasm_size) begin
            section_id = wasm_data[pos];
            pos++;
            section_size = read_leb128_u(pos);

            if (section_id == 9) begin  // Element section
                elem_count = read_leb128_u(pos);
                num_elem_segments = (elem_count > 16) ? 16 : elem_count;

                for (seg_idx = 0; seg_idx < elem_count; seg_idx++) begin
                    // Element segment format depends on flags
                    flags = read_leb128_u(pos);

                    if (flags == 0) begin
                        // flags=0: Active, table 0, offset expr, vec of func idx
                        // Active segments are implicitly dropped after instantiation
                        table_idx = 0;
                        opcode = wasm_data[pos];
                        pos++;
                        if (opcode == 8'h41) begin  // i32.const
                            offset_val = read_leb128_s(pos);
                        end else begin
                            offset_val = 0;
                        end
                        if (wasm_data[pos] == 8'h0B) pos++;  // end

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = 8'h70;
                            elem_segments[seg_idx].is_passive = 0;  // Active = dropped
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            func_idx_val = read_leb128_u(pos);
                            if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                            if (offset_val + f < 256 && table_idx < 4) begin
                                elem_entries[table_idx][offset_val + f] = func_idx_val;
                                if (offset_val + f + 1 > num_elements[table_idx]) begin
                                    num_elements[table_idx] = offset_val + f + 1;
                                end
                            end
                        end
                    end else if (flags == 1) begin
                        // flags=1: Passive, elemkind, vec of funcidx
                        elemtype = wasm_data[pos];
                        pos++;  // elemkind (0x00 = funcref)

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = 8'h70;  // funcref
                            elem_segments[seg_idx].is_passive = 1;  // Passive = available
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            func_idx_val = read_leb128_u(pos);
                            if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                        end
                    end else if (flags == 2) begin
                        // flags=2: Active, explicit table, offset expr, elemkind, vec of funcidx
                        table_idx = read_leb128_u(pos);
                        opcode = wasm_data[pos];
                        pos++;
                        if (opcode == 8'h41) begin
                            offset_val = read_leb128_s(pos);
                        end else begin
                            offset_val = 0;
                        end
                        if (wasm_data[pos] == 8'h0B) pos++;

                        elemtype = wasm_data[pos];
                        pos++;  // elemkind

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = 8'h70;
                            elem_segments[seg_idx].is_passive = 0;  // Active = dropped
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            func_idx_val = read_leb128_u(pos);
                            if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                            if (offset_val + f < 256 && table_idx < 4) begin
                                elem_entries[table_idx][offset_val + f] = func_idx_val;
                                if (offset_val + f + 1 > num_elements[table_idx]) begin
                                    num_elements[table_idx] = offset_val + f + 1;
                                end
                            end
                        end
                    end else if (flags == 3) begin
                        // flags=3: Declarative, elemkind, vec of funcidx
                        elemtype = wasm_data[pos];
                        pos++;  // elemkind

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = 8'h70;
                            elem_segments[seg_idx].is_passive = 0;  // Declarative = dropped
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            func_idx_val = read_leb128_u(pos);
                            if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                        end
                    end else if (flags == 4) begin
                        // flags=4: Active, table 0, offset expr, vec of elem exprs
                        table_idx = 0;
                        opcode = wasm_data[pos];
                        pos++;
                        if (opcode == 8'h41) begin
                            offset_val = read_leb128_s(pos);
                        end else begin
                            offset_val = 0;
                        end
                        if (wasm_data[pos] == 8'h0B) pos++;

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = 8'h70;
                            elem_segments[seg_idx].is_passive = 0;  // Active = dropped
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            opcode = wasm_data[pos];
                            pos++;
                            if (opcode == 8'hD2) begin  // ref.func
                                func_idx_val = read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                                if (offset_val + f < 256 && table_idx < 4) begin
                                    elem_entries[table_idx][offset_val + f] = func_idx_val;
                                    if (offset_val + f + 1 > num_elements[table_idx]) begin
                                        num_elements[table_idx] = offset_val + f + 1;
                                    end
                                end
                            end else if (opcode == 8'hD0) begin  // ref.null
                                read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = -1;
                                if (offset_val + f < 256 && table_idx < 4) begin
                                    elem_entries[table_idx][offset_val + f] = -1;
                                    if (offset_val + f + 1 > num_elements[table_idx]) begin
                                        num_elements[table_idx] = offset_val + f + 1;
                                    end
                                end
                            end else begin
                                if (wasm_data[pos] == 8'h0B) pos++;
                            end
                        end
                    end else if (flags == 5) begin
                        // flags=5: Passive, elemtype, vec of elem exprs
                        elemtype = wasm_data[pos];
                        pos++;
                        if (elemtype == 8'h63 || elemtype == 8'h64) begin
                            read_leb128_s(pos);  // skip heaptype
                        end

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = (elemtype == 8'h6F) ? 8'h6F : 8'h70;
                            elem_segments[seg_idx].is_passive = 1;  // Passive = available
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            opcode = wasm_data[pos];
                            pos++;
                            if (opcode == 8'hD2) begin  // ref.func
                                func_idx_val = read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                            end else if (opcode == 8'hD0) begin  // ref.null
                                read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = -1;
                            end else begin
                                while (wasm_data[pos] != 8'h0B && pos < wasm_size) pos++;
                                if (wasm_data[pos] == 8'h0B) pos++;
                            end
                        end
                    end else if (flags == 6) begin
                        // flags=6: Active, explicit table, offset expr, elemtype, vec of elem exprs
                        table_idx = read_leb128_u(pos);
                        opcode = wasm_data[pos];
                        pos++;
                        if (opcode == 8'h41) begin
                            offset_val = read_leb128_s(pos);
                        end else begin
                            offset_val = 0;
                        end
                        if (wasm_data[pos] == 8'h0B) pos++;

                        elemtype = wasm_data[pos];
                        pos++;
                        if (elemtype == 8'h63 || elemtype == 8'h64) begin
                            read_leb128_s(pos);
                        end

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = (elemtype == 8'h6F) ? 8'h6F : 8'h70;
                            elem_segments[seg_idx].is_passive = 0;  // Active = dropped
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            opcode = wasm_data[pos];
                            pos++;
                            if (opcode == 8'hD2) begin
                                func_idx_val = read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                                if (offset_val + f < 256 && table_idx < 4) begin
                                    elem_entries[table_idx][offset_val + f] = func_idx_val;
                                    if (offset_val + f + 1 > num_elements[table_idx]) begin
                                        num_elements[table_idx] = offset_val + f + 1;
                                    end
                                end
                            end else if (opcode == 8'hD0) begin
                                read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = -1;
                                if (offset_val + f < 256 && table_idx < 4) begin
                                    elem_entries[table_idx][offset_val + f] = -1;
                                    if (offset_val + f + 1 > num_elements[table_idx]) begin
                                        num_elements[table_idx] = offset_val + f + 1;
                                    end
                                end
                            end else begin
                                if (wasm_data[pos] == 8'h0B) pos++;
                            end
                        end
                    end else if (flags == 7) begin
                        // flags=7: Declarative, elemtype, vec of elem exprs
                        elemtype = wasm_data[pos];
                        pos++;
                        if (elemtype == 8'h63 || elemtype == 8'h64) begin
                            read_leb128_s(pos);
                        end

                        num_funcs = read_leb128_u(pos);
                        if (seg_idx < 16) begin
                            elem_segments[seg_idx].size = num_funcs;
                            elem_segments[seg_idx].elem_type = (elemtype == 8'h6F) ? 8'h6F : 8'h70;
                            elem_segments[seg_idx].is_passive = 0;  // Declarative = dropped
                        end

                        for (int f = 0; f < num_funcs; f++) begin
                            int func_idx_val;
                            opcode = wasm_data[pos];
                            pos++;
                            if (opcode == 8'hD2) begin
                                func_idx_val = read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = func_idx_val;
                            end else if (opcode == 8'hD0) begin
                                read_leb128_u(pos);
                                if (wasm_data[pos] == 8'h0B) pos++;
                                if (seg_idx < 16) elem_segments[seg_idx].entries[f] = -1;
                            end else begin
                                while (wasm_data[pos] != 8'h0B && pos < wasm_size) pos++;
                                if (wasm_data[pos] == 8'h0B) pos++;
                            end
                        end
                    end else begin
                        // Unknown flags - try to continue but warn
                        $display("Warning: Unknown element segment flags %d", flags);
                        break;
                    end
                end
                return;
            end else begin
                pos = pos + section_size;
            end
        end
    endtask

    // Load table metadata (size, max size, type, and base address) into CPU
    task automatic load_table_metadata();
        for (int t = 0; t < 4; t++) begin
            // Initialize table even if size is 0 (to set max_size and type)
            // Use declared_min_size for init, not num_elements (which may have been inflated by element segments)
            if (declared_min_size[t] > 0 || max_elements[t] > 0 || table_types[t] != 8'h70) begin
                @(posedge clk);
                table_init_en = 1;
                table_init_idx = t[1:0];
                table_init_size = declared_min_size[t][15:0];
                table_init_max_size = max_elements[t][15:0];
                // Set base address for this table in linear memory
                table_init_base = TB_TABLE_BASE + (t * TB_TABLE_STRIDE);
                // Map table_types (0x70=funcref, 0x6F=externref) to valtype_t
                case (table_types[t])
                    8'h6F: table_init_type = 4'h6;  // TYPE_EXTERNREF
                    default: table_init_type = 4'h5;  // TYPE_FUNCREF
                endcase
                // Track current size for table.grow handling
                current_table_size[t] = declared_min_size[t];
            end
        end
        @(posedge clk);
        table_init_en = 0;
    endtask

    // Load elements into linear memory (tables are now memory-backed)
    // Elements are written as 32-bit values at table_base + elem_idx * 4
    task automatic load_elements();
        automatic logic [31:0] base_addr;
        automatic logic [31:0] elem_addr;
        automatic logic [31:0] elem_val;

        for (int t = 0; t < 4; t++) begin
            base_addr = TB_TABLE_BASE + (t * TB_TABLE_STRIDE);
            for (int e = 0; e < num_elements[t]; e++) begin
                elem_addr = base_addr + (e << 2);  // base + e * 4
                // Convert -1 (null) to REF_NULL_VALUE (0xFFFFFFFF)
                elem_val = (elem_entries[t][e] == -1) ? 32'hFFFFFFFF : elem_entries[t][e][31:0];
                // Write 4 bytes directly to linear memory (little-endian)
                // wasm_memory uses byte-addressable memory
                linear_memory.mem[elem_addr + 0] = elem_val[7:0];
                linear_memory.mem[elem_addr + 1] = elem_val[15:8];
                linear_memory.mem[elem_addr + 2] = elem_val[23:16];
                linear_memory.mem[elem_addr + 3] = elem_val[31:24];
            end
        end
        // No clock cycles needed - direct memory access
        elem_init_en = 0;
    endtask

    // Load element segment data into linear memory (for table.init)
    // Element segments are stored at TB_ELEM_SEG_BASE + (seg_idx * TB_ELEM_SEG_STRIDE)
    task automatic load_elem_segments();
        automatic logic [31:0] base_addr;
        automatic logic [31:0] elem_addr;
        automatic logic [31:0] elem_val;

        for (int s = 0; s < num_elem_segments && s < 16; s++) begin
            base_addr = TB_ELEM_SEG_BASE + (s * TB_ELEM_SEG_STRIDE);
            for (int e = 0; e < elem_segments[s].size && e < 256; e++) begin
                elem_addr = base_addr + (e << 2);  // base + e * 4
                // Convert -1 (null) to REF_NULL_VALUE (0xFFFFFFFF)
                elem_val = (elem_segments[s].entries[e] == -1) ? 32'hFFFFFFFF : elem_segments[s].entries[e][31:0];

                // Write 4 bytes directly to linear memory (little-endian)
                linear_memory.mem[elem_addr + 0] = elem_val[7:0];
                linear_memory.mem[elem_addr + 1] = elem_val[15:8];
                linear_memory.mem[elem_addr + 2] = elem_val[23:16];
                linear_memory.mem[elem_addr + 3] = elem_val[31:24];
            end
        end
    endtask

    // Load element segment metadata into CPU (for table.init/elem.drop)
    task automatic load_elem_seg_metadata();
        for (int s = 0; s < num_elem_segments && s < 16; s++) begin
            @(posedge clk);
            elem_seg_init_en = 1;
            elem_seg_init_idx = s[3:0];
            elem_seg_init_base = TB_ELEM_SEG_BASE + (s * TB_ELEM_SEG_STRIDE);
            elem_seg_init_size = elem_segments[s].size[15:0];
            // Map elem_type (0x70=funcref, 0x6F=externref) to valtype_t
            case (elem_segments[s].elem_type)
                8'h6F: elem_seg_init_type = 4'h6;  // TYPE_EXTERNREF
                default: elem_seg_init_type = 4'h5;  // TYPE_FUNCREF
            endcase
            // Active/declarative segments are dropped; passive are not
            elem_seg_init_dropped = !elem_segments[s].is_passive;
        end
        @(posedge clk);
        elem_seg_init_en = 0;
    endtask

    // Load types into the CPU's type table (for multi-value block types)
    task automatic load_types();
        for (int i = 0; i < num_types; i++) begin
            @(posedge clk);
            type_init_en = 1;
            type_init_idx = i[7:0];
            type_init_param_count = type_info[i].param_count[7:0];
            type_init_result_count = type_info[i].result_count[7:0];
            type_init_param_types = type_info[i].param_types[31:0];
            type_init_result_types = type_info[i].result_types[31:0];
        end
        @(posedge clk);
        type_init_en = 0;
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
    // Format: <func_idx> <test_mode> <num_args> [<arg_type> <arg_hex>]... <num_results> [<result_type> <result_hex>]...
    // test_mode: 0=verify result, 1=expect trap, 2=run only (void function)
    // arg_type/result_type: 0=i32, 1=i64, 2=f32, 3=f64
    task automatic parse_testlist(input string filename);
        int fd;
        int func_id;
        int test_mode, nargs, nresults;
        int arg_type, result_type;
        longint arg_val, result_val;

        num_tests = 0;
        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("Cannot open test list file: %s", filename);
            return;
        end

        while (!$feof(fd)) begin
            int n;
            n = $fscanf(fd, "%d %d %d", func_id, test_mode, nargs);
            if (n >= 3) begin
                test_func_list[num_tests] = func_id;
                test_mode_list[num_tests] = test_mode;
                test_num_args[num_tests] = nargs;

                // Read arguments
                for (int a = 0; a < nargs && a < 32; a++) begin
                    if ($fscanf(fd, " %d %h", arg_type, arg_val) == 2) begin
                        test_arg_types[num_tests][a] = arg_type;
                        test_arg_values[num_tests][a] = arg_val;
                    end
                end

                // Read number of expected results
                if ($fscanf(fd, " %d", nresults) == 1) begin
                    test_num_results[num_tests] = nresults;
                    // Read expected results
                    for (int r = 0; r < nresults && r < 16; r++) begin
                        if ($fscanf(fd, " %d %h", result_type, result_val) == 2) begin
                            test_result_types[num_tests][r] = result_type;
                            test_result_values[num_tests][r] = result_val;
                        end
                    end
                end else begin
                    test_num_results[num_tests] = 0;
                end

                num_tests++;
            end
        end
        $fclose(fd);
    endtask

    // Run a single test invocation
    // test_mode: 0=verify result, 1=expect trap, 2=run only (void function)
    task automatic run_invocation(
        input int func_id,
        input int test_mode,
        input int num_args,
        input int arg_types [0:31],
        input longint arg_values [0:31],
        input int num_results,
        input int exp_result_types [0:15],
        input longint exp_result_values [0:15],
        output int passed
    );
        int cycles;
        int all_match;

        passed = 0;

        // Reset stacks before setting up arguments
        @(posedge clk);
        stack_reset_en = 1;
        @(posedge clk);
        stack_reset_en = 0;

        // Clear locals 0-63 to zero (WebAssembly requires declared locals to be 0)
        for (int i = 0; i < 64; i++) begin
            @(posedge clk);
            local_init_wr_en = 1;
            local_init_wr_base = 16'h0;
            local_init_wr_idx = i[7:0];
            local_init_wr_data.vtype = TYPE_I32;
            local_init_wr_data.value = 64'h0;
        end
        @(posedge clk);
        local_init_wr_en = 0;

        // Write arguments to locals (parameters are locals 0, 1, 2, ...)
        // local_base will be set to 0 (stack_ptr after reset)
        for (int a = 0; a < num_args; a++) begin
            @(posedge clk);
            local_init_wr_en = 1;
            local_init_wr_base = 16'h0;  // Entry function uses local_base = 0
            local_init_wr_idx = a[7:0];
            // Map arg type: 0=i32, 1=i64, 2=f32, 3=f64, 5=funcref, 6=externref
            case (arg_types[a])
                0: local_init_wr_data.vtype = TYPE_I32;
                1: local_init_wr_data.vtype = TYPE_I64;
                2: local_init_wr_data.vtype = TYPE_F32;
                3: local_init_wr_data.vtype = TYPE_F64;
                5: local_init_wr_data.vtype = TYPE_FUNCREF;
                6: local_init_wr_data.vtype = TYPE_EXTERNREF;
                default: local_init_wr_data.vtype = TYPE_I32;
            endcase
            local_init_wr_data.value = arg_values[a];
        end
        @(posedge clk);
        local_init_wr_en = 0;

        @(posedge clk);
        entry_func = func_id;
        ext_halt_i = 1;  // Enable trap handling for table.grow
        start = 1;
        @(posedge clk);
        start = 0;

        // Wait for halted to go low (CPU has started)
        @(posedge clk);

        cycles = 0;
        // Continue while: not halted, OR halted but waiting in ext_halt (need to handle trap)
        while ((!halted || ext_halted_o) && cycles < 10000000) begin
            @(posedge clk);
            cycles++;

            // Debug: print every 100000 cycles only (to avoid spam)
            // if (cycles % 100000 == 0)
            //     $display("DEBUG cycle %0d: halted=%b ext_halted_o=%b trapped=%b trap_code=%0d",
            //              cycles, halted, ext_halted_o, trapped, trap_code);

            // Handle S-mode traps - testbench acts as supervisor
            if (ext_halted_o) begin
                // Handle different trap types
                if (trap_code == TRAP_MEMORY_GROW) begin
                    // Memory grow - import_arg0 is requested delta, import_arg1 is current pages,
                    // import_arg2 is max pages (from module declaration, 0 = unlimited)
                    automatic int unsigned requested_delta = import_arg0_o;
                    automatic int unsigned current_pages = import_arg1_o;
                    automatic int unsigned max_pages = import_arg2_o;
                    automatic int unsigned new_pages = current_pages + requested_delta;
                    automatic int unsigned fallback_max = 1024;  // 64MB fallback limit

                    // Use module's max_pages if specified, otherwise use fallback
                    automatic int unsigned effective_max = (max_pages > 0) ? max_pages : fallback_max;

                    // Approve growth if it doesn't exceed effective limits
                    if (new_pages <= effective_max && new_pages >= current_pages) begin
                        ext_resume_val_i = current_pages;  // Return old size (success)
                    end else begin
                        ext_resume_val_i = 32'hFFFFFFFF;   // Return -1 (failure)
                    end
                    @(posedge clk);
                    ext_resume_i = 1;
                    @(posedge clk);
                    ext_resume_i = 0;
                    ext_resume_val_i = 0;
                end else if (trap_code == TRAP_IMPORT) begin
                    // Import call - return 0 for now (may need proper WASI handling)
                    ext_resume_val_i = 32'h0;
                    @(posedge clk);
                    ext_resume_i = 1;
                    @(posedge clk);
                    ext_resume_i = 0;
                    ext_resume_val_i = 0;
                end else if (trap_code == TRAP_TABLE_GROW) begin
                automatic int tbl_idx = table_grow_table_idx_o;
                automatic int unsigned delta = table_grow_delta_o;  // Unsigned to handle large values
                automatic int unsigned old_size = current_table_size[tbl_idx];
                automatic int unsigned new_size = old_size + delta;
                automatic int unsigned max_size = max_elements[tbl_idx];
                automatic int unsigned table_mem_limit = TB_TABLE_STRIDE >> 2;  // Max entries that fit in memory
                // $display("DEBUG: table.grow trap: tbl=%0d delta=%0d old_size=%0d new_size=%0d max_size=%0d",
                //          tbl_idx, delta, old_size, new_size, max_size);

                // Check if growth is allowed:
                // 1. new_size must not exceed max_size (if max_size > 0)
                // 2. new_size must not exceed memory allocation
                // 3. Check for overflow (new_size < old_size means overflow)
                if ((max_size == 0 || new_size <= max_size) &&
                    new_size <= table_mem_limit &&
                    new_size >= old_size) begin
                    // Growth allowed - update size and return old size
                    current_table_size[tbl_idx] = new_size;
                    // Initialize new entries to null in memory
                    for (int e = old_size; e < new_size; e++) begin
                        automatic logic [31:0] elem_addr = TB_TABLE_BASE + (tbl_idx * TB_TABLE_STRIDE) + (e << 2);
                        // Write null (0xFFFFFFFF) as 4 bytes little-endian
                        linear_memory.mem[elem_addr + 0] = 8'hFF;
                        linear_memory.mem[elem_addr + 1] = 8'hFF;
                        linear_memory.mem[elem_addr + 2] = 8'hFF;
                        linear_memory.mem[elem_addr + 3] = 8'hFF;
                    end
                    ext_resume_val_i = old_size;
                end else begin
                    // Growth not allowed - return -1
                    ext_resume_val_i = 32'hFFFFFFFF;
                end
                // $display("DEBUG: resuming with val=%h", ext_resume_val_i);
                // Wait one cycle for CPU to fully enter STATE_EXT_HALT
                // (ext_halted_o goes high during STATE_TRAP transition)
                @(posedge clk);
                ext_resume_i = 1;
                @(posedge clk);
                ext_resume_i = 0;
                ext_resume_val_i = 0;
                // $display("DEBUG: after resume, halted=%b ext_halted_o=%b", halted, ext_halted_o);
                end else begin
                    // Unknown trap type - just resume (might cause failures)
                    $display("WARNING: Unknown trap code %0d in ext_halt, resuming with 0", trap_code);
                    ext_resume_val_i = 32'h0;
                    @(posedge clk);
                    ext_resume_i = 1;
                    @(posedge clk);
                    ext_resume_i = 0;
                    ext_resume_val_i = 0;
                end
            end
        end
        ext_halt_i = 0;

        case (test_mode)
            0: begin  // Normal test - verify all results
                if (trapped) begin
                    passed = 0;
                end else if (num_results == 0) begin
                    // No results expected - pass if not trapped
                    passed = 1;
                end else begin
                    // Check all results match
                    all_match = 1;
                    for (int r = 0; r < num_results && r < 16; r++) begin
                        // Check based on type (32-bit vs 64-bit comparison)
                        if (exp_result_types[r] == 1 || exp_result_types[r] == 3) begin
                            // i64 or f64 - full 64-bit comparison
                            if (result_values[r].value != exp_result_values[r])
                                all_match = 0;
                        end else begin
                            // i32 or f32 - 32-bit comparison
                            if (result_values[r].value[31:0] != exp_result_values[r][31:0])
                                all_match = 0;
                        end
                    end
                    passed = all_match;
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
        int init_mem_max_pages;
        int passed, total_passed, total_failed;
        int test_passed;

        rst_n = 0;
        start = 0;
        code_wr_en = 0;
        func_wr_en = 0;
        entry_func = 0;
        mem_init_en = 0;
        mem_init_pages = 0;
        mem_init_max_pages = 0;
        mem_data_wr_en = 0;
        mem_data_wr_addr = 0;
        mem_data_wr_data = 0;
        stack_init_en = 0;
        stack_init_data = '0;
        stack_reset_en = 0;
        local_init_wr_en = 0;
        local_init_wr_base = 0;
        local_init_wr_idx = 0;
        local_init_wr_data = '0;
        global_init_en = 0;
        global_init_idx = 0;
        global_init_data = '0;
        table_init_en = 0;
        table_init_idx = 0;
        table_init_size = 0;
        table_init_max_size = 0;
        table_init_type = 0;
        table_init_base = 0;
        elem_init_en = 0;
        elem_init_table_idx = 0;
        elem_init_idx = 0;
        elem_init_value = 0;
        elem_seg_init_en = 0;
        elem_seg_init_idx = 0;
        elem_seg_init_base = 0;
        elem_seg_init_size = 0;
        elem_seg_init_type = 0;
        elem_seg_init_dropped = 0;
        data_seg_init_en = 0;
        data_seg_init_idx = 0;
        data_seg_init_base = 0;
        data_seg_init_size = 0;
        data_seg_init_dropped = 0;

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

        // Extract memory size and max
        extract_memory_info(init_mem_pages, init_mem_max_pages);

        // Reset
        @(posedge clk);
        @(posedge clk);
        rst_n = 1;
        @(posedge clk);

        // Initialize memory size and max
        @(posedge clk);
        mem_init_en = 1;
        mem_init_pages = init_mem_pages;
        mem_init_max_pages = init_mem_max_pages;
        @(posedge clk);
        mem_init_en = 0;
        mem_init_pages = 0;
        // Keep mem_init_max_pages set - it's used by TRAP_MEMORY_GROW to check limits
        @(posedge clk);

        // Extract and load data segments
        // Note: Passive data segments are stored at high addresses (TB_DATA_SEG_BASE = 0x14000)
        // which requires physical memory backing but does NOT change the wasm-visible memory size.
        // The memory module's MAX_PAGES parameter provides sufficient physical storage.
        extract_data_segments();
        load_data_segments();
        load_data_segment_metadata();

        // Extract and load global variables
        extract_globals();
        load_globals();

        // Extract table declarations (section 4) and element segments (section 9)
        extract_tables();
        extract_elements();

        // Ensure at least 1 page of memory is allocated if tables exist
        // (tables are stored in linear memory at TB_TABLE_BASE = 0xF000 which requires 1 page)
        if (init_mem_pages == 0 && (declared_min_size[0] > 0 || num_elements[0] > 0 ||
                                     declared_min_size[1] > 0 || num_elements[1] > 0 ||
                                     declared_min_size[2] > 0 || num_elements[2] > 0 ||
                                     declared_min_size[3] > 0 || num_elements[3] > 0)) begin
            @(posedge clk);
            mem_init_en = 1;
            mem_init_pages = 1;  // Allocate 1 page (64KB) for table storage
            mem_init_max_pages = (init_mem_max_pages == 0) ? 1 : init_mem_max_pages;
            @(posedge clk);
            mem_init_en = 0;
            $display("NOTE: Allocated 1 memory page for table storage");
        end

        load_table_metadata();
        load_elements();

        // Load element segment data and metadata for table.init/elem.drop
        // Element segments are stored at 0x10000+ (requires 2+ pages)
        // Only load if we have enough memory to avoid breaking tests
        if (num_elem_segments > 0 && init_mem_pages >= 2) begin
            load_elem_segments();
            load_elem_seg_metadata();
        end else if (num_elem_segments > 0) begin
            // Initialize metadata only (segments won't be accessible for table.init,
            // but elem.drop will work for dropping active/declarative segments)
            load_elem_seg_metadata();
        end

        if (use_testlist) begin
            // Multi-test mode: extract all functions
            extract_all_functions();

            // Load all code
            load_all_code();

            // Register all functions with proper offsets
            register_functions_from_wasm();

            // Load types (for multi-value block types)
            load_types();

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
                // Copy arguments and expected results for this test into local arrays
                automatic int local_arg_types [0:31];
                automatic longint local_arg_values [0:31];
                automatic int local_result_types [0:15];
                automatic longint local_result_values [0:15];
                for (int a = 0; a < 32; a++) begin
                    local_arg_types[a] = test_arg_types[t][a];
                    local_arg_values[a] = test_arg_values[t][a];
                end
                for (int r = 0; r < 16; r++) begin
                    local_result_types[r] = test_result_types[t][r];
                    local_result_values[r] = test_result_values[t][r];
                end

                run_invocation(
                    test_func_list[t],
                    test_mode_list[t],
                    test_num_args[t],
                    local_arg_types,
                    local_arg_values,
                    test_num_results[t],
                    local_result_types,
                    local_result_values,
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
                        $display("FAIL: test %0d func %0d (unexpected trap, code=%0d)",
                            t, test_func_list[t], trap_code);
                    end else begin
                        // Show first mismatched result
                        $display("FAIL: test %0d func %0d expected %0h, got %0h (result_count=%0d, result_valid=%0d)",
                            t, test_func_list[t], local_result_values[0],
                            result_values[0].value, result_count, result_valid);
                    end
                end
            end

            if (total_failed == 0) begin
                $display("PASS: %s (%0d tests)", wasm_file, total_passed);
            end else begin
                $display("FAIL: %s (%0d passed, %0d failed)", wasm_file, total_passed, total_failed);
            end

        end else begin
            // Single-test mode: use full module loading (just like multi-test mode)
            extract_all_functions();
            load_all_code();
            register_functions_from_wasm();

            // Set up single expected result for backward compatibility
            // Use test arrays index 0 which is zero-initialized
            test_result_types[0][0] = is_i64 ? 1 : 0;
            test_result_values[0][0] = expected_value;

            // Run the test (using test arrays index 0 as scratch)
            // These are already zero-initialized
            run_invocation(
                func_idx,
                expect_trap ? 1 : 0,  // test_mode: 0=verify result, 1=expect trap
                0,  // num_args (single-test mode doesn't support arguments)
                test_arg_types[0],
                test_arg_values[0],
                expect_trap ? 0 : 1,  // num_results: 0 for trap, 1 for normal
                test_result_types[0],
                test_result_values[0],
                test_passed
            );

            // Report result
            if (test_passed) begin
                if (expect_trap) begin
                    $display("PASS: %s (trapped as expected)", wasm_file);
                end else begin
                    $display("PASS: %s = %0d", wasm_file, is_i64 ? result_value.value : result_value.value[31:0]);
                end
            end else begin
                if (expect_trap) begin
                    $display("FAIL: %s (expected trap, got %0d)", wasm_file, result_value.value);
                end else if (trapped) begin
                    $display("FAIL: %s (unexpected trap)", wasm_file);
                end else begin
                    $display("FAIL: %s expected %0d, got %0d", wasm_file,
                        is_i64 ? expected_value : expected_value[31:0],
                        is_i64 ? result_values[0].value : result_values[0].value[31:0]);
                end
            end
        end

        $finish;
    end

endmodule
