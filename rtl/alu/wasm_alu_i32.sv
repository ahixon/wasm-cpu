// WebAssembly 32-bit Integer ALU
// Implements all i32 operations

module wasm_alu_i32
    import wasm_pkg::*;
(
    input  logic        clk,
    input  logic        rst_n,

    // Operation inputs
    input  logic        valid_in,
    input  alu_op_t     op,
    input  logic [31:0] operand_a,
    input  logic [31:0] operand_b,

    // Results
    output logic        valid_out,
    output logic [31:0] result,
    output trap_t       trap
);

    // Signed interpretations
    wire signed [31:0] a_signed = $signed(operand_a);
    wire signed [31:0] b_signed = $signed(operand_b);

    // Division results
    logic [31:0] div_s_result, div_u_result;
    logic [31:0] rem_s_result, rem_u_result;
    logic        div_by_zero, div_overflow;

    // Division by zero and overflow detection
    assign div_by_zero = (operand_b == 0);
    assign div_overflow = (operand_a == 32'h80000000) && (operand_b == 32'hFFFFFFFF);

    // Safe division
    always_comb begin
        if (div_by_zero) begin
            div_s_result = 32'h0;
            div_u_result = 32'h0;
            rem_s_result = 32'h0;
            rem_u_result = 32'h0;
        end else begin
            div_u_result = operand_a / operand_b;
            rem_u_result = operand_a % operand_b;
            if (div_overflow) begin
                div_s_result = 32'h80000000;  // Result is -2^31
                rem_s_result = 32'h0;
            end else begin
                div_s_result = $signed(a_signed / b_signed);
                rem_s_result = $signed(a_signed % b_signed);
            end
        end
    end

    // Main ALU logic
    always_comb begin
        result = 32'h0;
        trap = TRAP_NONE;

        case (op)
            // Arithmetic
            ALU_ADD:    result = operand_a + operand_b;
            ALU_SUB:    result = operand_a - operand_b;
            ALU_MUL:    result = operand_a * operand_b;

            ALU_DIV_S: begin
                if (div_by_zero) trap = TRAP_INT_DIV_ZERO;
                else if (div_overflow) trap = TRAP_INT_OVERFLOW;
                else result = div_s_result;
            end

            ALU_DIV_U: begin
                if (div_by_zero) trap = TRAP_INT_DIV_ZERO;
                else result = div_u_result;
            end

            ALU_REM_S: begin
                if (div_by_zero) trap = TRAP_INT_DIV_ZERO;
                else result = rem_s_result;
            end

            ALU_REM_U: begin
                if (div_by_zero) trap = TRAP_INT_DIV_ZERO;
                else result = rem_u_result;
            end

            // Bitwise
            ALU_AND:    result = operand_a & operand_b;
            ALU_OR:     result = operand_a | operand_b;
            ALU_XOR:    result = operand_a ^ operand_b;

            // Shifts (shift amount is mod 32)
            ALU_SHL:    result = operand_a << operand_b[4:0];
            ALU_SHR_S:  result = $signed(a_signed >>> operand_b[4:0]);
            ALU_SHR_U:  result = operand_a >> operand_b[4:0];

            // Rotations
            ALU_ROTL:   result = rotl32(operand_a, operand_b[4:0]);
            ALU_ROTR:   result = rotr32(operand_a, operand_b[4:0]);

            // Unary operations
            ALU_CLZ:    result = {26'b0, clz32(operand_a)};
            ALU_CTZ:    result = {26'b0, ctz32(operand_a)};
            ALU_POPCNT: result = {26'b0, popcnt32(operand_a)};

            // Comparison - return 1 (true) or 0 (false)
            ALU_EQZ:    result = {31'b0, operand_a == 32'h0};
            ALU_EQ:     result = {31'b0, operand_a == operand_b};
            ALU_NE:     result = {31'b0, operand_a != operand_b};
            ALU_LT_S:   result = {31'b0, a_signed < b_signed};
            ALU_LT_U:   result = {31'b0, operand_a < operand_b};
            ALU_GT_S:   result = {31'b0, a_signed > b_signed};
            ALU_GT_U:   result = {31'b0, operand_a > operand_b};
            ALU_LE_S:   result = {31'b0, a_signed <= b_signed};
            ALU_LE_U:   result = {31'b0, operand_a <= operand_b};
            ALU_GE_S:   result = {31'b0, a_signed >= b_signed};
            ALU_GE_U:   result = {31'b0, operand_a >= operand_b};

            default:    result = 32'h0;
        endcase
    end

    // Valid output follows valid input (combinational)
    assign valid_out = valid_in;

endmodule
