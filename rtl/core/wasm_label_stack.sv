// WebAssembly Label Stack
// Manages structured control flow labels for block/loop/if constructs

module wasm_label_stack
    import wasm_pkg::*;
#(
    parameter int DEPTH = LABEL_STACK_DEPTH
)(
    input  logic        clk,
    input  logic        rst_n,

    // Push interface (entering block/loop/if)
    input  logic        push_en,
    input  label_entry_t push_data,

    // Pop interface (leaving block via end)
    input  logic        pop_en,
    output label_entry_t pop_data,

    // Branch interface (br/br_if/br_table)
    input  logic [7:0]  branch_depth,  // How many labels to pop
    output label_entry_t branch_target, // Target label info

    // Multi-pop for branch
    input  logic        branch_pop_en,

    // Stack manipulation for call/return
    input  logic        set_sp_en,
    input  logic [7:0]  set_sp_value,

    // Status
    output logic [7:0]  stack_ptr,
    output logic        empty,
    output logic        full
);

    // Label stack memory
    label_entry_t label_mem [0:DEPTH-1];

    // Stack pointer
    logic [7:0] sp;

    // Outputs
    assign stack_ptr = sp;
    assign empty = (sp == 0);
    assign full = (sp >= DEPTH);

    // Pop data (top of stack)
    assign pop_data = (sp > 0) ? label_mem[sp - 1] : '0;

    // Branch target (sp - 1 - branch_depth)
    wire [7:0] target_idx = sp - 1 - branch_depth;
    assign branch_target = (branch_depth < sp) ? label_mem[target_idx] : '0;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sp <= '0;
        end else begin
            if (set_sp_en) begin
                sp <= set_sp_value;
            end
            else if (branch_pop_en) begin
                // Pop labels up to and including target
                if (branch_depth < sp) begin
                    sp <= sp - branch_depth - 1;
                end
            end
            else if (push_en && pop_en) begin
                label_mem[sp - 1] <= push_data;
            end
            else if (push_en && !full) begin
                label_mem[sp] <= push_data;
                sp <= sp + 1;
            end
            else if (pop_en && !empty) begin
                sp <= sp - 1;
            end
        end
    end

endmodule
