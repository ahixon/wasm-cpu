// WebAssembly Global Variables Storage
// Manages module-level global variables

module wasm_globals
    import wasm_pkg::*;
#(
    parameter int NUM_GLOBALS = 256
)(
    input  logic        clk,
    input  logic        rst_n,

    // Read interface
    input  logic        rd_en,
    input  logic [7:0]  rd_idx,
    output stack_entry_t rd_data,
    output logic        rd_valid,

    // Write interface
    input  logic        wr_en,
    input  logic [7:0]  wr_idx,
    input  stack_entry_t wr_data,
    output logic        wr_valid,
    output logic        wr_error,  // Attempted write to immutable global

    // Initialization interface
    input  logic        init_en,
    input  logic [7:0]  init_idx,
    input  global_entry_t init_data,

    // Status
    output logic [7:0]  num_globals
);

    // Global storage
    global_entry_t globals [0:NUM_GLOBALS-1];

    // Count of initialized globals
    logic [7:0] global_count;
    assign num_globals = global_count;

    // Read logic
    always_comb begin
        rd_data = '0;
        rd_valid = 1'b0;
        if (rd_en && rd_idx < global_count) begin
            rd_data.vtype = globals[rd_idx].vtype;
            rd_data.value = globals[rd_idx].value;
            rd_valid = 1'b1;
        end
    end

    // Write logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            global_count <= 8'h0;
            wr_valid <= 1'b0;
            wr_error <= 1'b0;
            for (int i = 0; i < NUM_GLOBALS; i++) begin
                globals[i] <= '0;
            end
        end else begin
            wr_valid <= 1'b0;
            wr_error <= 1'b0;

            // Initialization
            if (init_en && init_idx < NUM_GLOBALS) begin
                globals[init_idx] <= init_data;
                if (init_idx >= global_count) begin
                    global_count <= init_idx + 1;
                end
            end

            // Runtime write
            if (wr_en && wr_idx < global_count) begin
                if (globals[wr_idx].mutable_flag) begin
                    globals[wr_idx].value <= wr_data.value;
                    wr_valid <= 1'b1;
                end else begin
                    wr_error <= 1'b1;
                end
            end
        end
    end

endmodule
