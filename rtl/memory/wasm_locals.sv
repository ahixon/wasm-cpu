// WebAssembly Local Variables Storage
// Manages function local variables (including parameters)

module wasm_locals
    import wasm_pkg::*;
#(
    parameter int MAX_LOCALS = LOCAL_COUNT * CALL_STACK_DEPTH
)(
    input  logic        clk,
    input  logic        rst_n,

    // Read interface
    input  logic        rd_en,
    input  logic [15:0] base_idx,    // Base index (from call frame)
    input  logic [7:0]  local_idx,   // Local index within function
    output stack_entry_t rd_data,
    output logic        rd_valid,

    // Write interface
    input  logic        wr_en,
    input  logic [15:0] wr_base_idx,
    input  logic [7:0]  wr_local_idx,
    input  stack_entry_t wr_data,
    output logic        wr_valid,

    // Bulk initialization for function entry
    input  logic        init_en,
    input  logic [15:0] init_base,
    input  logic [7:0]  init_count,
    input  valtype_t    init_types [0:31],  // Types for initialization

    // Status
    output logic [15:0] next_free_base
);

    // Local storage
    stack_entry_t locals [0:MAX_LOCALS-1];

    // Track next available base
    logic [15:0] free_base;
    assign next_free_base = free_base;

    // Read address calculation
    wire [15:0] rd_addr = base_idx + {8'b0, local_idx};
    wire [15:0] wr_addr = wr_base_idx + {8'b0, wr_local_idx};

    // Read logic (combinational)
    always_comb begin
        rd_data = '0;
        rd_valid = 1'b0;
        if (rd_en && rd_addr < MAX_LOCALS) begin
            rd_data = locals[rd_addr];
            rd_valid = 1'b1;
        end
    end

    // Write logic (sequential)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            free_base <= 16'h0;
            wr_valid <= 1'b0;
            for (int i = 0; i < MAX_LOCALS; i++) begin
                locals[i] = '0;
            end
        end else begin
            wr_valid <= 1'b0;

            // Bulk initialization for function entry
            if (init_en) begin
                for (int i = 0; i < 32 && i < init_count; i++) begin
                    if (init_base + i < MAX_LOCALS) begin
                        locals[init_base + i].vtype <= init_types[i];
                        locals[init_base + i].value <= 64'h0;
                    end
                end
                if (init_base + {8'b0, init_count} > free_base) begin
                    free_base <= init_base + {8'b0, init_count};
                end
            end

            // Single write
            if (wr_en && wr_addr < MAX_LOCALS) begin
                locals[wr_addr] <= wr_data;
                wr_valid <= 1'b1;
            end
        end
    end

endmodule
