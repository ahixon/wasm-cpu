// WebAssembly 32-bit Floating Point Unit
// Implements all f32 operations following IEEE 754

module wasm_fpu_f32
    import wasm_pkg::*;
(
    input  logic        clk,
    input  logic        rst_n,

    // Operation inputs
    input  logic        valid_in,
    input  fpu_op_t     op,
    input  logic [31:0] operand_a,
    input  logic [31:0] operand_b,

    // Results
    output logic        valid_out,
    output logic [31:0] result,
    output trap_t       trap
);

    // IEEE 754 single precision format
    // [31]    = sign
    // [30:23] = exponent (biased by 127)
    // [22:0]  = mantissa (implicit leading 1)

    // Extract fields
    wire        sign_a = operand_a[31];
    wire [7:0]  exp_a  = operand_a[30:23];
    wire [22:0] mant_a = operand_a[22:0];

    wire        sign_b = operand_b[31];
    wire [7:0]  exp_b  = operand_b[30:23];
    wire [22:0] mant_b = operand_b[22:0];

    // Special value detection
    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 23'h0);
    wire b_is_zero     = (exp_b == 8'h00) && (mant_b == 23'h0);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 23'h0);
    wire b_is_inf      = (exp_b == 8'hFF) && (mant_b == 23'h0);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 23'h0);
    wire b_is_nan      = (exp_b == 8'hFF) && (mant_b != 23'h0);
    wire a_is_snan     = a_is_nan && !mant_a[22];  // Signaling NaN
    wire b_is_snan     = b_is_nan && !mant_b[22];

    // Canonical NaN (quiet NaN)
    localparam [31:0] CANONICAL_NAN = 32'h7FC00000;
    localparam [31:0] POS_ZERO = 32'h00000000;
    localparam [31:0] NEG_ZERO = 32'h80000000;
    localparam [31:0] POS_INF  = 32'h7F800000;
    localparam [31:0] NEG_INF  = 32'hFF800000;

    // Convert f32 bits to f64 bits for use with $bitstoreal
    // f32: 1 sign, 8 exp (bias 127), 23 mantissa
    // f64: 1 sign, 11 exp (bias 1023), 52 mantissa
    function automatic logic [63:0] f32_to_f64_bits(input logic [31:0] f32);
        logic        sign_f;
        logic [7:0]  exp_f;
        logic [22:0] mant_f;
        logic [10:0] exp_d;
        logic [51:0] mant_d;
        int          shift;
        logic [23:0] norm_mant;

        sign_f = f32[31];
        exp_f  = f32[30:23];
        mant_f = f32[22:0];

        if (exp_f == 8'hFF) begin
            // Infinity or NaN
            exp_d = 11'h7FF;
            mant_d = {mant_f, 29'b0};  // Preserve NaN payload
        end
        else if (exp_f == 8'h00) begin
            // Zero or subnormal
            if (mant_f == 23'h0) begin
                // Zero
                exp_d = 11'h000;
                mant_d = 52'h0;
            end
            else begin
                // Subnormal f32 - normalize it for f64
                // f32 subnormal value = 0.mant_f * 2^(-126)
                // = mant_f * 2^(-126-23) = mant_f * 2^(-149)
                // For mant_f = 1: value = 2^(-149)
                // In f64: 1.0 * 2^(-149) has exp_d = -149 + 1023 = 874
                // For mant_f = 2^i (bit i set): value = 2^(-149+i), exp_d = 874 + i

                // Find leading 1 position (0 to 22)
                shift = 0;
                for (int i = 22; i >= 0; i--) begin
                    if (mant_f[i]) begin
                        shift = i;  // Position of leading 1
                        break;
                    end
                end
                // exp_d = 874 + shift
                exp_d = 11'd874 + shift;
                // After normalization, leading 1 becomes implicit
                // Shift left to align, then mask off the leading 1
                // For shift=0, mant=0x000001: shift left by 22 to get 0x400000, mask to get 0x000000
                // For shift=1, mant=0x000002: shift left by 21 to get 0x400000, mask to get 0x000000
                // For shift=1, mant=0x000003: shift left by 21 to get 0x600000, mask to get 0x200000
                mant_d = {((mant_f << (22 - shift)) & 23'h3FFFFF), 29'b0};
            end
        end
        else begin
            // Normal number: adjust exponent bias (127 -> 1023, diff = 896)
            exp_d = {3'b0, exp_f} + 11'd896;
            mant_d = {mant_f, 29'b0};
        end

        return {sign_f, exp_d, mant_d};
    endfunction

    // Convert f64 bits back to f32 bits with proper rounding
    function automatic logic [31:0] f64_to_f32_bits(input logic [63:0] f64);
        logic        sign_d;
        logic [10:0] exp_d;
        logic [51:0] mant_d;
        logic [7:0]  exp_f;
        logic [22:0] mant_f;
        logic        round_bit, sticky_bit, lsb;
        logic [23:0] mant_rounded;

        sign_d = f64[63];
        exp_d  = f64[62:52];
        mant_d = f64[51:0];

        if (exp_d == 11'h7FF) begin
            // Infinity or NaN
            exp_f = 8'hFF;
            mant_f = mant_d[51:29];  // Truncate mantissa for NaN
        end
        else if (exp_d == 11'h000) begin
            // Zero or subnormal f64
            exp_f = 8'h00;
            mant_f = mant_d[51:29];
        end
        else begin
            // Normal: check if in f32 range
            if (exp_d < 11'd874) begin
                // Underflow to zero (too small even for subnormal)
                exp_f = 8'h00;
                mant_f = 23'h0;
            end
            else if (exp_d < 11'd897) begin
                // Subnormal f32 range (exp_d 874 to 896 inclusive)
                exp_f = 8'h00;
                // TODO: proper rounding for subnormals
                mant_f = ({1'b1, mant_d[51:29]} >> (11'd897 - exp_d));
            end
            else if (exp_d > 11'd896 + 11'd254) begin
                // Overflow to infinity
                exp_f = 8'hFF;
                mant_f = 23'h0;
            end
            else begin
                // Normal f32 range - apply round-to-nearest-ties-to-even
                exp_f = exp_d - 11'd896;

                // Round bit is bit 28, sticky is OR of bits 27:0
                round_bit = mant_d[28];
                sticky_bit = |mant_d[27:0];
                lsb = mant_d[29];  // LSB of result mantissa

                // Round up if: round && (sticky || lsb)
                // This implements ties-to-even: when round=1 and sticky=0,
                // we only round up if lsb=1 (making result even)
                if (round_bit && (sticky_bit || lsb)) begin
                    mant_rounded = mant_d[51:29] + 1'b1;
                    // Check for mantissa overflow (e.g., 0x7FFFFF + 1 = 0x800000)
                    if (mant_rounded[23]) begin
                        // Mantissa overflowed, increment exponent
                        exp_f = exp_f + 1'b1;
                        mant_f = 23'h0;  // mantissa becomes 0 after overflow
                        // Check for exponent overflow to infinity
                        if (exp_f == 8'hFF) begin
                            mant_f = 23'h0;
                        end
                    end
                    else begin
                        mant_f = mant_rounded[22:0];
                    end
                end
                else begin
                    mant_f = mant_d[51:29];
                end
            end
        end

        return {sign_d, exp_f, mant_f};
    endfunction

    // Comparison helper - handles NaN correctly
    function automatic logic f32_lt(input logic [31:0] a, input logic [31:0] b);
        if (a_is_nan || b_is_nan) return 1'b0;
        // Both positive
        if (!a[31] && !b[31]) return a < b;
        // Both negative
        if (a[31] && b[31]) return a > b;
        // a negative, b positive
        if (a[31] && !b[31]) begin
            // Handle -0 == +0
            if (a_is_zero && b_is_zero) return 1'b0;
            return 1'b1;
        end
        // a positive, b negative
        if (a_is_zero && b_is_zero) return 1'b0;
        return 1'b0;
    endfunction

    function automatic logic f32_gt(input logic [31:0] a, input logic [31:0] b);
        return f32_lt(b, a);
    endfunction

    function automatic logic f32_eq(input logic [31:0] a, input logic [31:0] b);
        if (a_is_nan || b_is_nan) return 1'b0;
        // +0 == -0
        if (a_is_zero && b_is_zero) return 1'b1;
        return a == b;
    endfunction

    // Main FPU logic
    always_comb begin
        result = 32'h0;
        trap = TRAP_NONE;

        case (op)
            FPU_ADD: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf && b_is_inf && (sign_a != sign_b)) result = CANONICAL_NAN;
                else if (a_is_inf) result = operand_a;
                else if (b_is_inf) result = operand_b;
                else begin
                    // Convert f32 to f64, do arithmetic, convert back
                    real ra, rb, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rb = $bitstoreal(f32_to_f64_bits(operand_b));
                    rr = ra + rb;
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_SUB: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf && b_is_inf && (sign_a == sign_b)) result = CANONICAL_NAN;
                else if (a_is_inf) result = operand_a;
                else if (b_is_inf) result = {~sign_b, operand_b[30:0]};
                else begin
                    real ra, rb, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rb = $bitstoreal(f32_to_f64_bits(operand_b));
                    rr = ra - rb;
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_MUL: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if ((a_is_inf && b_is_zero) || (a_is_zero && b_is_inf)) result = CANONICAL_NAN;
                else if (a_is_inf || b_is_inf) result = {sign_a ^ sign_b, 8'hFF, 23'h0};
                else begin
                    real ra, rb, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rb = $bitstoreal(f32_to_f64_bits(operand_b));
                    rr = ra * rb;
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_DIV: begin
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf && b_is_inf) result = CANONICAL_NAN;
                else if (a_is_zero && b_is_zero) result = CANONICAL_NAN;
                else if (b_is_zero) result = {sign_a ^ sign_b, 8'hFF, 23'h0}; // Inf
                else if (a_is_inf) result = {sign_a ^ sign_b, 8'hFF, 23'h0};
                else if (b_is_inf) result = {sign_a ^ sign_b, 31'h0}; // Zero
                else begin
                    real ra, rb, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rb = $bitstoreal(f32_to_f64_bits(operand_b));
                    rr = ra / rb;
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_MIN: begin
                // WebAssembly: min with any NaN returns canonical NaN
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_zero && b_is_zero) result = sign_a ? operand_a : operand_b; // -0 < +0
                else begin
                    real ra, rb;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rb = $bitstoreal(f32_to_f64_bits(operand_b));
                    result = (ra < rb) ? operand_a : operand_b;
                end
            end

            FPU_MAX: begin
                // WebAssembly: max with any NaN returns canonical NaN
                if (a_is_nan || b_is_nan) result = CANONICAL_NAN;
                else if (a_is_zero && b_is_zero) result = sign_a ? operand_b : operand_a;
                else begin
                    real ra, rb;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rb = $bitstoreal(f32_to_f64_bits(operand_b));
                    result = (ra > rb) ? operand_a : operand_b;
                end
            end

            FPU_ABS: begin
                result = {1'b0, operand_a[30:0]};
            end

            FPU_NEG: begin
                result = {~operand_a[31], operand_a[30:0]};
            end

            FPU_CEIL: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rr = $ceil(ra);
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_FLOOR: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rr = $floor(ra);
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_TRUNC: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rr = (ra >= 0) ? $floor(ra) : $ceil(ra);
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_NEAREST: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (a_is_inf || a_is_zero) result = operand_a;
                else begin
                    // Check if magnitude is >= 2^23 (already an integer in f32)
                    if (exp_a >= 8'd150) begin
                        // Value is already an integer (no fractional part)
                        result = operand_a;
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(f32_to_f64_bits(operand_a));
                        // Round half to even using floor(x + 0.5) for positive,
                        // and special handling for exact halves
                        if (ra >= 0.0) begin
                            rr = $floor(ra + 0.5);
                            // Ties to even: if exactly 0.5, round to even
                            if (ra - $floor(ra) == 0.5) begin
                                if ($rtoi(rr) % 2 != 0) rr = rr - 1.0;
                            end
                        end
                        else begin
                            rr = $ceil(ra - 0.5);
                            // Ties to even: if exactly -0.5, round to even
                            if ($ceil(ra) - ra == 0.5) begin
                                if ($rtoi(rr) % 2 != 0) rr = rr + 1.0;
                            end
                        end
                        // Preserve negative zero
                        if (rr == 0.0 && sign_a)
                            result = NEG_ZERO;
                        else
                            result = f64_to_f32_bits($realtobits(rr));
                    end
                end
            end

            FPU_SQRT: begin
                if (a_is_nan) result = CANONICAL_NAN;
                else if (sign_a && !a_is_zero) result = CANONICAL_NAN; // sqrt of negative
                else if (a_is_inf) result = operand_a;
                else if (a_is_zero) result = operand_a;
                else begin
                    real ra, rr;
                    ra = $bitstoreal(f32_to_f64_bits(operand_a));
                    rr = $sqrt(ra);
                    result = f64_to_f32_bits($realtobits(rr));
                end
            end

            FPU_COPYSIGN: begin
                result = {operand_b[31], operand_a[30:0]};
            end

            // Comparisons return i32 (0 or 1)
            FPU_EQ: begin
                result = {31'b0, f32_eq(operand_a, operand_b)};
            end

            FPU_NE: begin
                result = {31'b0, !f32_eq(operand_a, operand_b)};
            end

            FPU_LT: begin
                result = {31'b0, f32_lt(operand_a, operand_b)};
            end

            FPU_GT: begin
                result = {31'b0, f32_gt(operand_a, operand_b)};
            end

            FPU_LE: begin
                result = {31'b0, f32_lt(operand_a, operand_b) || f32_eq(operand_a, operand_b)};
            end

            FPU_GE: begin
                result = {31'b0, f32_gt(operand_a, operand_b) || f32_eq(operand_a, operand_b)};
            end

            default: result = 32'h0;
        endcase
    end

    assign valid_out = valid_in;

endmodule
