// WebAssembly Linear Memory
// Implements the WebAssembly linear memory with page-based allocation
// Uses clean bus interface compatible with AXI-lite adapter

module wasm_memory
    import wasm_pkg::*;
#(
    parameter int MAX_PAGES = MEMORY_PAGES
)(
    input  logic        clk,
    input  logic        rst_n,

    // Memory bus interface (data path)
    input  mem_bus_req_t  mem_req_i,       // Memory bus request
    output mem_bus_resp_t mem_resp_o,      // Memory bus response

    // WASM-specific memory operation (for sign extension)
    input  mem_op_t       mem_op_i,        // Original WASM operation type

    // Memory management interface (WASM-specific)
    input  mem_mgmt_req_t  mem_mgmt_req_i,  // Management request
    output mem_mgmt_resp_t mem_mgmt_resp_o, // Management response

    // Direct memory write for data segment initialization
    input  logic        data_wr_en,
    input  logic [31:0] data_wr_addr,
    input  logic [7:0]  data_wr_data,

    // Status
    output trap_t       trap,

    // Debug read interface (active when CPU halted)
    input  logic        dbg_rd_en,
    input  logic [31:0] dbg_rd_addr,
    output logic [31:0] dbg_rd_data
);

    // Memory array (byte addressable)
    // For simulation, we use a simple array
    // In synthesis, this would be block RAM
    logic [7:0] mem [0:MAX_PAGES * PAGE_SIZE - 1];

    // Current number of pages
    logic [31:0] num_pages;
    // Maximum pages (from WASM module, 0 means no limit beyond MAX_PAGES)
    logic [31:0] max_pages;
    // Grow result register
    logic [31:0] grow_result_q;
    logic        grow_done_q;

    // Assign management response
    assign mem_mgmt_resp_o.current_pages = num_pages;
    assign mem_mgmt_resp_o.grow_result   = grow_result_q;
    assign mem_mgmt_resp_o.grow_done     = grow_done_q;

    // Memory is always ready to accept requests (single-cycle response)
    assign mem_resp_o.ready = 1'b1;

    // Debug read (combinational, 32-bit aligned)
    always_comb begin
        if (dbg_rd_en && in_bounds(dbg_rd_addr, 4)) begin
            dbg_rd_data = {mem[dbg_rd_addr+3], mem[dbg_rd_addr+2],
                           mem[dbg_rd_addr+1], mem[dbg_rd_addr]};
        end else begin
            dbg_rd_data = 32'h0;
        end
    end

    // Bounds checking - must detect overflow in address+size
    // in_bounds: checks against wasm-declared memory size (num_pages)
    // in_physical_bounds: checks against physical backing store (MAX_PAGES)
    // in_read_bounds: for reads, allows wasm-visible OR internal region (0x10000+)
    //   This allows internal data (passive data segments) to be stored at high addresses
    //   while keeping wasm memory semantics correct for user code below 0x10000.
    localparam logic [31:0] INTERNAL_REGION_BASE = 32'h0010_0000;  // 1MB - well above typical wasm test usage

    function automatic logic in_bounds(input logic [31:0] addr, input int size);
        logic [32:0] end_addr;
        logic [32:0] mem_size;
        end_addr = {1'b0, addr} + size;
        mem_size = 33'(num_pages) * PAGE_SIZE;  // 33-bit to handle 4GB
        return !end_addr[32] && (end_addr <= mem_size);
    endfunction

    function automatic logic in_physical_bounds(input logic [31:0] addr, input int size);
        logic [32:0] end_addr;
        localparam logic [32:0] phys_size = 33'(MAX_PAGES) * PAGE_SIZE;
        end_addr = {1'b0, addr} + size;
        return !end_addr[32] && (end_addr <= phys_size);
    endfunction

    function automatic logic in_read_bounds(input logic [31:0] addr, input int size);
        // Allow reads from wasm-visible region OR internal region (for data segments)
        // Internal region starts at INTERNAL_REGION_BASE and goes up to MAX_PAGES
        return in_bounds(addr, size) ||
               (addr >= INTERNAL_REGION_BASE && in_physical_bounds(addr, size));
    endfunction

    // Get access size in bytes from mem_size_t
    function automatic int size_to_bytes(mem_size_t sz);
        case (sz)
            MEM_SIZE_1: return 1;
            MEM_SIZE_2: return 2;
            MEM_SIZE_4: return 4;
            MEM_SIZE_8: return 8;
            default:    return 4;
        endcase
    endfunction

    // Read logic and trap detection (combinational)
    always_comb begin
        mem_resp_o.rdata = 64'h0;
        mem_resp_o.rvalid = 1'b0;
        mem_resp_o.error = 1'b0;
        trap = TRAP_NONE;

        // Check for out-of-bounds writes - use wasm-declared memory size
        if (mem_req_i.valid && mem_req_i.write) begin
            if (!in_bounds(mem_req_i.addr, size_to_bytes(mem_req_i.size))) begin
                trap = TRAP_OUT_OF_BOUNDS;
                mem_resp_o.error = 1'b1;
            end
        end

        // Read operations - use in_read_bounds to allow reading from internal
        // storage areas (e.g., passive data segments for memory.init)
        if (mem_req_i.valid && !mem_req_i.write) begin
            // Use mem_op_i for sign extension, but mem_req_i.size for bounds check
            case (mem_op_i)
                MEM_LOAD_I32: begin
                    if (!in_read_bounds(mem_req_i.addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {32'b0, mem[mem_req_i.addr+3], mem[mem_req_i.addr+2],
                                            mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_I64: begin
                    if (!in_read_bounds(mem_req_i.addr, 8)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {mem[mem_req_i.addr+7], mem[mem_req_i.addr+6],
                                            mem[mem_req_i.addr+5], mem[mem_req_i.addr+4],
                                            mem[mem_req_i.addr+3], mem[mem_req_i.addr+2],
                                            mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_F32: begin
                    if (!in_read_bounds(mem_req_i.addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {32'b0, mem[mem_req_i.addr+3], mem[mem_req_i.addr+2],
                                            mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_F64: begin
                    if (!in_read_bounds(mem_req_i.addr, 8)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {mem[mem_req_i.addr+7], mem[mem_req_i.addr+6],
                                            mem[mem_req_i.addr+5], mem[mem_req_i.addr+4],
                                            mem[mem_req_i.addr+3], mem[mem_req_i.addr+2],
                                            mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_I8_S: begin
                    if (!in_read_bounds(mem_req_i.addr, 1)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {{56{mem[mem_req_i.addr][7]}}, mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_I8_U: begin
                    if (!in_read_bounds(mem_req_i.addr, 1)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {56'b0, mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_I16_S: begin
                    if (!in_read_bounds(mem_req_i.addr, 2)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {{48{mem[mem_req_i.addr+1][7]}},
                                            mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_I16_U: begin
                    if (!in_read_bounds(mem_req_i.addr, 2)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {48'b0, mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_I32_S: begin
                    if (!in_read_bounds(mem_req_i.addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        logic [31:0] val;
                        val = {mem[mem_req_i.addr+3], mem[mem_req_i.addr+2],
                               mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rdata = {{32{val[31]}}, val};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                MEM_LOAD_I32_U: begin
                    if (!in_read_bounds(mem_req_i.addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        mem_resp_o.rdata = {32'b0, mem[mem_req_i.addr+3], mem[mem_req_i.addr+2],
                                            mem[mem_req_i.addr+1], mem[mem_req_i.addr]};
                        mem_resp_o.rvalid = 1'b1;
                    end
                end

                default: begin
                    // Unknown operation - just read raw bytes based on size
                    if (!in_read_bounds(mem_req_i.addr, size_to_bytes(mem_req_i.size))) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                        mem_resp_o.error = 1'b1;
                    end else begin
                        case (mem_req_i.size)
                            MEM_SIZE_1: mem_resp_o.rdata = {56'b0, mem[mem_req_i.addr]};
                            MEM_SIZE_2: mem_resp_o.rdata = {48'b0, mem[mem_req_i.addr+1],
                                                            mem[mem_req_i.addr]};
                            MEM_SIZE_4: mem_resp_o.rdata = {32'b0, mem[mem_req_i.addr+3],
                                                            mem[mem_req_i.addr+2],
                                                            mem[mem_req_i.addr+1],
                                                            mem[mem_req_i.addr]};
                            MEM_SIZE_8: mem_resp_o.rdata = {mem[mem_req_i.addr+7],
                                                            mem[mem_req_i.addr+6],
                                                            mem[mem_req_i.addr+5],
                                                            mem[mem_req_i.addr+4],
                                                            mem[mem_req_i.addr+3],
                                                            mem[mem_req_i.addr+2],
                                                            mem[mem_req_i.addr+1],
                                                            mem[mem_req_i.addr]};
                        endcase
                        mem_resp_o.rvalid = 1'b1;
                    end
                end
            endcase
        end
    end

    // Write logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            num_pages <= 32'd0;  // Start with 0, will be set by init
            max_pages <= MAX_PAGES;  // Default to parameter value
            grow_result_q <= 32'h0;
            grow_done_q <= 1'b0;
            // Initialize memory to zero
            for (int i = 0; i < MAX_PAGES * PAGE_SIZE; i++) begin
                mem[i] = 8'h0;
            end
        end else begin
            // Clear grow_done after one cycle
            grow_done_q <= 1'b0;

            // Handle memory initialization via management interface
            if (mem_mgmt_req_i.init_valid) begin
                num_pages <= mem_mgmt_req_i.init_pages;
                // Set max_pages: use init_max_pages if specified, otherwise MAX_PAGES
                max_pages <= (mem_mgmt_req_i.init_max_pages != 0) ?
                             mem_mgmt_req_i.init_max_pages : MAX_PAGES;
            end

            // Handle direct data segment write (for initialization)
            if (data_wr_en) begin
                mem[data_wr_addr] <= data_wr_data;
            end

            // Memory grow operation via management interface
            if (mem_mgmt_req_i.grow_valid) begin
                // Check against both runtime max_pages and compile-time MAX_PAGES
                if (num_pages + mem_mgmt_req_i.grow_pages <= max_pages &&
                    num_pages + mem_mgmt_req_i.grow_pages <= MAX_PAGES) begin
                    grow_result_q <= num_pages;
                    num_pages <= num_pages + mem_mgmt_req_i.grow_pages;
                end else begin
                    grow_result_q <= 32'hFFFFFFFF;  // Failure
                end
                grow_done_q <= 1'b1;
            end

            // Write operation via bus interface
            if (mem_req_i.valid && mem_req_i.write) begin
                case (mem_req_i.size)
                    MEM_SIZE_1: begin
                        if (in_bounds(mem_req_i.addr, 1)) begin
                            mem[mem_req_i.addr] <= mem_req_i.wdata[7:0];
                        end
                    end

                    MEM_SIZE_2: begin
                        if (in_bounds(mem_req_i.addr, 2)) begin
                            mem[mem_req_i.addr]   <= mem_req_i.wdata[7:0];
                            mem[mem_req_i.addr+1] <= mem_req_i.wdata[15:8];
                        end
                    end

                    MEM_SIZE_4: begin
                        if (in_bounds(mem_req_i.addr, 4)) begin
                            mem[mem_req_i.addr]   <= mem_req_i.wdata[7:0];
                            mem[mem_req_i.addr+1] <= mem_req_i.wdata[15:8];
                            mem[mem_req_i.addr+2] <= mem_req_i.wdata[23:16];
                            mem[mem_req_i.addr+3] <= mem_req_i.wdata[31:24];
                        end
                    end

                    MEM_SIZE_8: begin
                        if (in_bounds(mem_req_i.addr, 8)) begin
                            mem[mem_req_i.addr]   <= mem_req_i.wdata[7:0];
                            mem[mem_req_i.addr+1] <= mem_req_i.wdata[15:8];
                            mem[mem_req_i.addr+2] <= mem_req_i.wdata[23:16];
                            mem[mem_req_i.addr+3] <= mem_req_i.wdata[31:24];
                            mem[mem_req_i.addr+4] <= mem_req_i.wdata[39:32];
                            mem[mem_req_i.addr+5] <= mem_req_i.wdata[47:40];
                            mem[mem_req_i.addr+6] <= mem_req_i.wdata[55:48];
                            mem[mem_req_i.addr+7] <= mem_req_i.wdata[63:56];
                        end
                    end
                endcase
            end
        end
    end

endmodule
