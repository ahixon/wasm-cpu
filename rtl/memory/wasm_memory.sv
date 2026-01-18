// WebAssembly Linear Memory
// Implements the WebAssembly linear memory with page-based allocation

module wasm_memory
    import wasm_pkg::*;
#(
    parameter int MAX_PAGES = MEMORY_PAGES
)(
    input  logic        clk,
    input  logic        rst_n,

    // Initial memory configuration
    input  logic        init_en,        // Pulse to set initial size
    input  logic [31:0] init_pages,     // Initial page count
    input  logic [31:0] init_max_pages, // Max pages (0 = use MAX_PAGES parameter)

    // Direct memory write for data segment initialization
    input  logic        data_wr_en,
    input  logic [31:0] data_wr_addr,
    input  logic [7:0]  data_wr_data,

    // Read interface
    input  logic        rd_en,
    input  logic [31:0] rd_addr,
    input  mem_op_t     rd_op,
    output logic [63:0] rd_data,
    output logic        rd_valid,

    // Write interface
    input  logic        wr_en,
    input  logic [31:0] wr_addr,
    input  mem_op_t     wr_op,
    input  logic [63:0] wr_data,
    output logic        wr_valid,

    // Memory management
    input  logic        grow_en,
    input  logic [31:0] grow_pages,
    output logic [31:0] current_pages,
    output logic [31:0] grow_result,  // Previous size or -1 on failure

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

    assign current_pages = num_pages;

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
    function automatic logic in_bounds(input logic [31:0] addr, input int size);
        logic [32:0] end_addr;  // 33-bit to detect overflow
        end_addr = {1'b0, addr} + size;
        // Check for overflow (bit 32 set) or exceeds memory size
        return !end_addr[32] && (end_addr[31:0] <= (num_pages * PAGE_SIZE));
    endfunction

    // Read logic and trap detection (combinational)
    always_comb begin
        rd_data = 64'h0;
        rd_valid = 1'b0;
        trap = TRAP_NONE;

        // Check for out-of-bounds writes
        if (wr_en) begin
            case (wr_op)
                MEM_STORE_I32, MEM_STORE_I32_FROM_I64: begin
                    if (!in_bounds(wr_addr, 4)) trap = TRAP_OUT_OF_BOUNDS;
                end
                MEM_STORE_I64: begin
                    if (!in_bounds(wr_addr, 8)) trap = TRAP_OUT_OF_BOUNDS;
                end
                MEM_STORE_I8: begin
                    if (!in_bounds(wr_addr, 1)) trap = TRAP_OUT_OF_BOUNDS;
                end
                MEM_STORE_I16: begin
                    if (!in_bounds(wr_addr, 2)) trap = TRAP_OUT_OF_BOUNDS;
                end
                default: ;
            endcase
        end

        if (rd_en) begin
            case (rd_op)
                MEM_LOAD_I32: begin
                    if (!in_bounds(rd_addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {32'b0, mem[rd_addr+3], mem[rd_addr+2], mem[rd_addr+1], mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_I64: begin
                    if (!in_bounds(rd_addr, 8)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {mem[rd_addr+7], mem[rd_addr+6], mem[rd_addr+5], mem[rd_addr+4],
                                   mem[rd_addr+3], mem[rd_addr+2], mem[rd_addr+1], mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_F32: begin
                    if (!in_bounds(rd_addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {32'b0, mem[rd_addr+3], mem[rd_addr+2], mem[rd_addr+1], mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_F64: begin
                    if (!in_bounds(rd_addr, 8)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {mem[rd_addr+7], mem[rd_addr+6], mem[rd_addr+5], mem[rd_addr+4],
                                   mem[rd_addr+3], mem[rd_addr+2], mem[rd_addr+1], mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_I8_S: begin
                    if (!in_bounds(rd_addr, 1)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {{56{mem[rd_addr][7]}}, mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_I8_U: begin
                    if (!in_bounds(rd_addr, 1)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {56'b0, mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_I16_S: begin
                    if (!in_bounds(rd_addr, 2)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {{48{mem[rd_addr+1][7]}}, mem[rd_addr+1], mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_I16_U: begin
                    if (!in_bounds(rd_addr, 2)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {48'b0, mem[rd_addr+1], mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_I32_S: begin
                    if (!in_bounds(rd_addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        logic [31:0] val;
                        val = {mem[rd_addr+3], mem[rd_addr+2], mem[rd_addr+1], mem[rd_addr]};
                        rd_data = {{32{val[31]}}, val};
                        rd_valid = 1'b1;
                    end
                end

                MEM_LOAD_I32_U: begin
                    if (!in_bounds(rd_addr, 4)) begin
                        trap = TRAP_OUT_OF_BOUNDS;
                    end else begin
                        rd_data = {32'b0, mem[rd_addr+3], mem[rd_addr+2], mem[rd_addr+1], mem[rd_addr]};
                        rd_valid = 1'b1;
                    end
                end

                default: begin
                    trap = TRAP_NONE;
                end
            endcase
        end
    end

    // Write logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            num_pages <= 32'd0;  // Start with 0, will be set by init_en
            max_pages <= MAX_PAGES;  // Default to parameter value
            grow_result <= 32'h0;
            wr_valid <= 1'b0;
            // Initialize memory to zero
            for (int i = 0; i < MAX_PAGES * PAGE_SIZE; i++) begin
                mem[i] <= 8'h0;
            end
        end else begin
            // Handle memory initialization
            if (init_en) begin
                num_pages <= init_pages;
                // Set max_pages: use init_max_pages if specified, otherwise MAX_PAGES
                max_pages <= (init_max_pages != 0) ? init_max_pages : MAX_PAGES;
            end

            // Handle direct data segment write (for initialization)
            if (data_wr_en) begin
                mem[data_wr_addr] <= data_wr_data;
            end

            wr_valid <= 1'b0;
            // Note: grow_result is NOT reset here - it persists until next grow

            // Memory grow operation
            if (grow_en) begin
                // Check against both runtime max_pages and compile-time MAX_PAGES
                if (num_pages + grow_pages <= max_pages && num_pages + grow_pages <= MAX_PAGES) begin
                    grow_result <= num_pages;
                    num_pages <= num_pages + grow_pages;
                end else begin
                    grow_result <= 32'hFFFFFFFF;  // Failure
                end
            end

            // Write operation
            if (wr_en) begin
                case (wr_op)
                    MEM_STORE_I32, MEM_STORE_I32_FROM_I64: begin
                        if (in_bounds(wr_addr, 4)) begin
                            mem[wr_addr]   <= wr_data[7:0];
                            mem[wr_addr+1] <= wr_data[15:8];
                            mem[wr_addr+2] <= wr_data[23:16];
                            mem[wr_addr+3] <= wr_data[31:24];
                            wr_valid <= 1'b1;
                        end
                    end

                    MEM_STORE_I64: begin
                        if (in_bounds(wr_addr, 8)) begin
                            mem[wr_addr]   <= wr_data[7:0];
                            mem[wr_addr+1] <= wr_data[15:8];
                            mem[wr_addr+2] <= wr_data[23:16];
                            mem[wr_addr+3] <= wr_data[31:24];
                            mem[wr_addr+4] <= wr_data[39:32];
                            mem[wr_addr+5] <= wr_data[47:40];
                            mem[wr_addr+6] <= wr_data[55:48];
                            mem[wr_addr+7] <= wr_data[63:56];
                            wr_valid <= 1'b1;
                        end
                    end

                    MEM_STORE_I8: begin
                        if (in_bounds(wr_addr, 1)) begin
                            mem[wr_addr] <= wr_data[7:0];
                            wr_valid <= 1'b1;
                        end
                    end

                    MEM_STORE_I16: begin
                        if (in_bounds(wr_addr, 2)) begin
                            mem[wr_addr]   <= wr_data[7:0];
                            mem[wr_addr+1] <= wr_data[15:8];
                            wr_valid <= 1'b1;
                        end
                    end

                    default: begin
                        wr_valid <= 1'b0;
                    end
                endcase
            end
        end
    end

endmodule
