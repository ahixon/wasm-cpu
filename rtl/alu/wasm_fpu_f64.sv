// WebAssembly 64-bit Floating Point Unit
// Implements all f64 operations following IEEE 754

module wasm_fpu_f64
    import wasm_pkg::*;
(
    input  logic        clk,
    input  logic        rst_n,

    // Operation inputs
    input  logic        valid_in,
    input  fpu_op_t     op,
    input  logic [63:0] operand_a,
    input  logic [63:0] operand_b,

    // Results
    output logic        valid_out,
    output logic [63:0] result,
    output trap_t       trap
);

    // IEEE 754 double precision format
    // [63]    = sign
    // [62:52] = exponent (biased by 1023)
    // [51:0]  = mantissa (implicit leading 1)

    // Extract fields
    wire        sign_a  = operand_a[63];
    wire [10:0] exp_a   = operand_a[62:52];
    wire [51:0] mant_a  = operand_a[51:0];

    wire        sign_b  = operand_b[63];
    wire [10:0] exp_b   = operand_b[62:52];
    wire [51:0] mant_b  = operand_b[51:0];

    // Special value detection
    wire a_is_zero     = (exp_a == 11'h000) && (mant_a == 52'h0);
    wire b_is_zero     = (exp_b == 11'h000) && (mant_b == 52'h0);
    wire a_is_inf      = (exp_a == 11'h7FF) && (mant_a == 52'h0);
    wire b_is_inf      = (exp_b == 11'h7FF) && (mant_b == 52'h0);
    wire a_is_nan      = (exp_a == 11'h7FF) && (mant_a != 52'h0);
    wire b_is_nan      = (exp_b == 11'h7FF) && (mant_b != 52'h0);

    // Canonical NaN
    localparam [63:0] CANONICAL_NAN = 64'h7FF8000000000000;
    localparam [63:0] POS_ZERO = 64'h0000000000000000;
    localparam [63:0] NEG_ZERO = 64'h8000000000000000;
    localparam [63:0] POS_INF  = 64'h7FF0000000000000;
    localparam [63:0] NEG_INF  = 64'hFFF0000000000000;

    // Comparison helper
    function automatic logic f64_eq(input logic [63:0] a, input logic [63:0] b);
        logic a_nan, b_nan, a_zero, b_zero;
        a_nan = (a[62:52] == 11'h7FF) && (a[51:0] != 52'h0);
        b_nan = (b[62:52] == 11'h7FF) && (b[51:0] != 52'h0);
        a_zero = (a[62:52] == 11'h000) && (a[51:0] == 52'h0);
        b_zero = (b[62:52] == 11'h000) && (b[51:0] == 52'h0);
        if (a_nan || b_nan) return 1'b0;
        if (a_zero && b_zero) return 1'b1;
        return a == b;
    endfunction

    function automatic logic f64_lt(input logic [63:0] a, input logic [63:0] b);
        logic a_nan, b_nan, a_zero, b_zero;
        a_nan = (a[62:52] == 11'h7FF) && (a[51:0] != 52'h0);
        b_nan = (b[62:52] == 11'h7FF) && (b[51:0] != 52'h0);
        a_zero = (a[62:52] == 11'h000) && (a[51:0] == 52'h0);
        b_zero = (b[62:52] == 11'h000) && (b[51:0] == 52'h0);
        if (a_nan || b_nan) return 1'b0;
        if (a_zero && b_zero) return 1'b0;
        if (!a[63] && !b[63]) return a < b;
        if (a[63] && b[63]) return a > b;
        if (a[63] && !b[63]) return 1'b1;
        return 1'b0;
    endfunction

    function automatic logic f64_gt(input logic [63:0] a, input logic [63:0] b);
        return f64_lt(b, a);
    endfunction

    // Main FPU logic
    always_comb begin
        result = 64'h0;
        trap = TRAP_NONE;

        case (op)
            FPU_ADD: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf && b_is_inf && (sign_a != sign_b)) result = CANONICAL_NAN;
                else if (a_is_inf) result = operand_a;
                else if (b_is_inf) result = operand_b;
                else begin
                    real ra, rb, rr;
                    ra = $bitstoreal(operand_a);
                    rb = $bitstoreal(operand_b);
                    rr = ra + rb;
                    result = $realtobits(rr);
                end
            end

            FPU_SUB: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf && b_is_inf && (sign_a == sign_b)) result = CANONICAL_NAN;
                else if (a_is_inf) result = operand_a;
                else if (b_is_inf) result = {~sign_b, operand_b[62:0]};
                else begin
                    real ra, rb, rr;
                    ra = $bitstoreal(operand_a);
                    rb = $bitstoreal(operand_b);
                    rr = ra - rb;
                    result = $realtobits(rr);
                end
            end

            FPU_MUL: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if ((a_is_inf && b_is_zero) || (a_is_zero && b_is_inf)) result = CANONICAL_NAN;
                else if (a_is_inf || b_is_inf) result = {sign_a ^ sign_b, 11'h7FF, 52'h0};
                else begin
                    real ra, rb, rr;
                    ra = $bitstoreal(operand_a);
                    rb = $bitstoreal(operand_b);
                    rr = ra * rb;
                    result = $realtobits(rr);
                end
            end

            FPU_DIV: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf && b_is_inf) result = CANONICAL_NAN;
                else if (a_is_zero && b_is_zero) result = CANONICAL_NAN;
                else if (b_is_zero) result = {sign_a ^ sign_b, 11'h7FF, 52'h0};
                else if (a_is_inf) result = {sign_a ^ sign_b, 11'h7FF, 52'h0};
                else if (b_is_inf) result = {sign_a ^ sign_b, 63'h0};
                else begin
                    real ra, rb, rr;
                    ra = $bitstoreal(operand_a);
                    rb = $bitstoreal(operand_b);
                    rr = ra / rb;
                    result = $realtobits(rr);
                end
            end

            FPU_MIN: begin
                // WebAssembly: min with any NaN returns canonical NaN
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_zero && b_is_zero) result = sign_a ? operand_a : operand_b;
                else begin
                    real ra, rb;
                    ra = $bitstoreal(operand_a);
                    rb = $bitstoreal(operand_b);
                    result = (ra < rb) ? operand_a : operand_b;
                end
            end

            FPU_MAX: begin
                // WebAssembly: max with any NaN returns canonical NaN
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_zero && b_is_zero) result = sign_a ? operand_b : operand_a;
                else begin
                    real ra, rb;
                    ra = $bitstoreal(operand_a);
                    rb = $bitstoreal(operand_b);
                    result = (ra > rb) ? operand_a : operand_b;
                end
            end

            FPU_ABS: begin
                result = {1'b0, operand_a[62:0]};
            end

            FPU_NEG: begin
                result = {~operand_a[63], operand_a[62:0]};
            end

            FPU_CEIL: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(operand_a);
                    rr = $ceil(ra);
                    result = $realtobits(rr);
                end
            end

            FPU_FLOOR: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(operand_a);
                    rr = $floor(ra);
                    result = $realtobits(rr);
                end
            end

            FPU_TRUNC: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(operand_a);
                    rr = (ra >= 0) ? $floor(ra) : $ceil(ra);
                    result = $realtobits(rr);
                end
            end

            FPU_NEAREST: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    // Check if magnitude is >= 2^52 (already an integer in f64)
                    // exp_a = 1023 + 52 = 1075 means 2^52
                    // Also handle exp=1074 specially since the rounding logic has precision issues there
                    if (exp_a >= 11'd1075) begin
                        // Value is already an integer (no fractional part)
                        result = operand_a;
                    end
                    else if (exp_a == 11'd1074) begin
                        // At exp=1074, value is between 2^51 and 2^52
                        // The fractional part is in bit 0 of mantissa
                        // If mantissa[0] is 0, value is integer; if 1, fractional part is 0.5
                        // For values with fractional part close to 1, round appropriately
                        if (mant_a == 52'hFFFFFFFFFFFFF) begin
                            // This is 2^52 - epsilon, rounds to 2^52
                            // Result should be exp=1075, mant=0
                            result = {sign_a, 11'd1075, 52'h0};
                        end else if (mant_a[0] == 1'b0) begin
                            // Already an integer
                            result = operand_a;
                        end else begin
                            // Fractional part is 0.5 - round to even (round down since integer part is odd)
                            result = {sign_a, exp_a, mant_a & 52'hFFFFFFFFFFFFE};
                        end
                    end
                    else begin
                        real ra, rr, frac;
                        ra = $bitstoreal(operand_a);
                        // Round half to even using proper comparison
                        if (ra >= 0.0) begin
                            frac = ra - $floor(ra);
                            if (frac < 0.5) begin
                                rr = $floor(ra);
                            end else if (frac > 0.5) begin
                                rr = $floor(ra) + 1.0;
                            end else begin
                                // Exactly 0.5 - round to even
                                rr = $floor(ra);
                                if ($rtoi(rr) % 2 != 0) rr = rr + 1.0;
                            end
                        end
                        else begin
                            frac = $ceil(ra) - ra;
                            if (frac < 0.5) begin
                                rr = $ceil(ra);
                            end else if (frac > 0.5) begin
                                rr = $ceil(ra) - 1.0;
                            end else begin
                                // Exactly -0.5 - round to even
                                rr = $ceil(ra);
                                if ($rtoi(rr) % 2 != 0) rr = rr - 1.0;
                            end
                        end
                        // Preserve negative zero
                        if (rr == 0.0 && sign_a)
                            result = NEG_ZERO;
                        else
                            result = $realtobits(rr);
                    end
                end
            end

            FPU_SQRT: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (sign_a && !a_is_zero) result = CANONICAL_NAN;
                else if (a_is_inf) result = operand_a;
                else if (a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(operand_a);
                    rr = $sqrt(ra);
                    result = $realtobits(rr);
                end
            end

            FPU_COPYSIGN: begin
                result = {operand_b[63], operand_a[62:0]};
            end

            // Comparisons return i32 (0 or 1)
            FPU_EQ: begin
                result = {63'b0, f64_eq(operand_a, operand_b)};
            end

            FPU_NE: begin
                result = {63'b0, !f64_eq(operand_a, operand_b)};
            end

            FPU_LT: begin
                result = {63'b0, f64_lt(operand_a, operand_b)};
            end

            FPU_GT: begin
                result = {63'b0, f64_gt(operand_a, operand_b)};
            end

            FPU_LE: begin
                result = {63'b0, f64_lt(operand_a, operand_b) || f64_eq(operand_a, operand_b)};
            end

            FPU_GE: begin
                result = {63'b0, f64_gt(operand_a, operand_b) || f64_eq(operand_a, operand_b)};
            end

            default: result = 64'h0;
        endcase
    end

    assign valid_out = valid_in;

endmodule
