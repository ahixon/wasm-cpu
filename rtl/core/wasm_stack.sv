// WebAssembly Operand Stack
// Implements a LIFO stack for WebAssembly operand values
// Each entry is 68 bits: 4-bit type tag + 64-bit value

module wasm_stack
    import wasm_pkg::*;
#(
    parameter int DEPTH = STACK_DEPTH
)(
    input  logic        clk,
    input  logic        rst_n,

    // Push interface
    input  logic        push_en,
    input  stack_entry_t push_data,

    // Pop interface
    input  logic        pop_en,
    output stack_entry_t pop_data,

    // Peek interface (read without pop)
    input  logic [15:0] peek_offset,  // 0 = top, 1 = second from top, etc.
    output stack_entry_t peek_data,

    // Second peek interface for operations needing two reads
    input  logic [15:0] peek_offset2,
    output stack_entry_t peek_data2,

    // Multi-pop for function returns
    input  logic        multi_pop_en,
    input  logic [7:0]  multi_pop_count,

    // Stack manipulation
    input  logic        set_sp_en,
    input  logic [15:0] set_sp_value,

    // Status
    output logic [15:0] stack_ptr,
    output logic        empty,
    output logic        full,
    output trap_t       trap
);

    // Stack memory
    stack_entry_t stack_mem [0:DEPTH-1];

    // Stack pointer (points to next free slot)
    logic [15:0] sp;

    // Combinational outputs
    assign stack_ptr = sp;
    assign empty = (sp == 0);
    assign full = (sp >= DEPTH);

    // Pop data is top of stack (sp - 1)
    assign pop_data = (sp > 0) ? stack_mem[sp - 1] : '0;

    // Peek data at offset from top
    wire [15:0] peek_idx = sp - 1 - peek_offset;
    assign peek_data = (peek_offset < sp) ? stack_mem[peek_idx] : '0;

    // Second peek data at offset from top
    wire [15:0] peek_idx2 = sp - 1 - peek_offset2;
    assign peek_data2 = (peek_offset2 < sp) ? stack_mem[peek_idx2] : '0;

    // Trap detection
    always_comb begin
        trap = TRAP_NONE;
        if (push_en && full) begin
            trap = TRAP_STACK_OVERFLOW;
        end
        if (pop_en && empty) begin
            trap = TRAP_STACK_UNDERFLOW;
        end
        if (multi_pop_en && multi_pop_count > sp) begin
            trap = TRAP_STACK_UNDERFLOW;
        end
    end

    // Sequential logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sp <= '0;
        end else begin
            // Set SP takes priority
            if (set_sp_en) begin
                sp <= set_sp_value;
            end
            // Multi-pop
            else if (multi_pop_en) begin
                if (multi_pop_count <= sp) begin
                    sp <= sp - {8'b0, multi_pop_count};
                end
            end
            // Push and pop in same cycle
            else if (push_en && pop_en) begin
                // Pop first, then push to same location
                stack_mem[sp - 1] <= push_data;
                // SP unchanged
            end
            // Push only
            else if (push_en && !full) begin
                stack_mem[sp] <= push_data;
                sp <= sp + 1;
            end
            // Pop only
            else if (pop_en && !empty) begin
                sp <= sp - 1;
            end
        end
    end

endmodule
