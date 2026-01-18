// WebAssembly Call Stack
// Manages function call frames for call/return operations

module wasm_call_stack
    import wasm_pkg::*;
#(
    parameter int DEPTH = CALL_STACK_DEPTH
)(
    input  logic        clk,
    input  logic        rst_n,

    // Push interface (function call)
    input  logic        push_en,
    input  frame_entry_t push_data,

    // Pop interface (function return)
    input  logic        pop_en,
    output frame_entry_t pop_data,

    // Current frame peek
    output frame_entry_t current_frame,

    // Status
    output logic [7:0]  stack_ptr,
    output logic        empty,
    output logic        full,
    output trap_t       trap
);

    // Call stack memory
    frame_entry_t frame_mem [0:DEPTH-1];

    // Stack pointer
    logic [7:0] sp;

    // Outputs
    assign stack_ptr = sp;
    assign empty = (sp == 0);
    assign full = (sp >= DEPTH);

    // Pop data and current frame
    assign pop_data = (sp > 0) ? frame_mem[sp - 1] : '0;
    assign current_frame = (sp > 0) ? frame_mem[sp - 1] : '0;

    // Trap detection
    always_comb begin
        trap = TRAP_NONE;
        if (push_en && full) begin
            trap = TRAP_CALL_STACK_EXHAUSTED;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sp <= '0;
        end else begin
            if (push_en && pop_en) begin
                // Replace top
                frame_mem[sp - 1] <= push_data;
            end
            else if (push_en && !full) begin
                frame_mem[sp] <= push_data;
                sp <= sp + 1;
            end
            else if (pop_en && !empty) begin
                sp <= sp - 1;
            end
        end
    end

endmodule
