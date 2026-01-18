// WebAssembly Type Conversion Unit
// Implements all conversion operations between types

module wasm_conv
    import wasm_pkg::*;
(
    input  logic        clk,
    input  logic        rst_n,

    // Operation inputs
    input  logic        valid_in,
    input  opcode_t     op,
    input  logic [7:0]  sub_op,     // For extended opcodes (0xFC prefix)
    input  logic [63:0] operand,

    // Results
    output logic        valid_out,
    output logic [63:0] result,
    output trap_t       trap
);

    // Input helpers
    wire [31:0] f32_in = operand[31:0];
    wire [63:0] f64_in = operand;
    wire [31:0] i32_in = operand[31:0];
    wire [63:0] i64_in = operand;

    // Check for NaN/Inf in floats
    wire f32_is_nan = (f32_in[30:23] == 8'hFF) && (f32_in[22:0] != 0);
    wire f32_is_inf = (f32_in[30:23] == 8'hFF) && (f32_in[22:0] == 0);
    wire f64_is_nan = (f64_in[62:52] == 11'h7FF) && (f64_in[51:0] != 0);
    wire f64_is_inf = (f64_in[62:52] == 11'h7FF) && (f64_in[51:0] == 0);

    // Convert f32 bits to f64 bits (Verilator doesn't support shortreal properly)
    function automatic logic [63:0] f32_to_f64_bits(input logic [31:0] f32);
        logic        sign_f;
        logic [7:0]  exp_f;
        logic [22:0] mant_f;
        logic [10:0] exp_d;
        logic [51:0] mant_d;
        int          shift;

        sign_f = f32[31];
        exp_f  = f32[30:23];
        mant_f = f32[22:0];

        if (exp_f == 8'hFF) begin
            exp_d = 11'h7FF;
            mant_d = {mant_f, 29'b0};
        end
        else if (exp_f == 8'h00) begin
            if (mant_f == 23'h0) begin
                exp_d = 11'h000;
                mant_d = 52'h0;
            end
            else begin
                // Subnormal f32 - normalize for f64
                // Find position of leading 1 bit
                shift = 0;
                for (int i = 22; i >= 0; i--) begin
                    if (mant_f[i]) begin
                        shift = i;
                        break;
                    end
                end
                // Exponent: subnormal f32 has implicit exp of -126
                // After normalizing by shifting left (23-1-shift) positions,
                // the effective exponent becomes -126 - (22 - shift) = -126 + shift - 22
                // In f64 bias: -126 + shift - 22 + 1023 = 875 + shift
                // Wait, let me recalculate:
                // Subnormal value = mant_f * 2^(-149) where -149 = -126 - 23
                // Leading 1 at position 'shift' means value = 2^shift * (normalized mantissa) * 2^(-149)
                // = 1.xxx * 2^(shift - 149) (after normalization, the leading 1 is implicit)
                // Actually no: value = 2^shift * (1 + remaining_frac) * 2^(-23) * 2^(-126)
                //           = (1 + remaining_frac) * 2^(shift - 23 - 126)
                //           = (1 + remaining_frac) * 2^(shift - 149)
                // For f64: exp_unbiased = shift - 149, so exp_biased = shift - 149 + 1023 = shift + 874
                exp_d = 11'd874 + shift;
                // Mantissa: remove the leading 1 (at position shift), keep bits [shift-1:0]
                // These 'shift' bits need to be placed at the TOP of the 52-bit mantissa
                // Formula: result[51:52-shift] = mant_f[shift-1:0], rest = 0
                // This means shift left by (52 - shift) positions
                if (shift > 0) begin
                    logic [51:0] masked_mant;
                    masked_mant = {29'b0, mant_f} & ((52'b1 << shift) - 1);  // Keep only bits below leading 1
                    mant_d = masked_mant << (52 - shift);
                end else begin
                    // shift == 0 means only bit 0 was set, no mantissa bits left
                    mant_d = 52'h0;
                end
            end
        end
        else begin
            exp_d = {3'b0, exp_f} + 11'd896;
            mant_d = {mant_f, 29'b0};
        end

        return {sign_f, exp_d, mant_d};
    endfunction

    // Convert f64 bits to f32 bits with rounding
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
            exp_f = 8'hFF;
            mant_f = mant_d[51:29];
        end
        else if (exp_d == 11'h000) begin
            exp_f = 8'h00;
            mant_f = mant_d[51:29];
        end
        else begin
            if (exp_d < 11'd873) begin
                // Definitely underflow to zero
                exp_f = 8'h00;
                mant_f = 23'h0;
            end
            else if (exp_d < 11'd897) begin
                // Subnormal f32 result - apply proper rounding
                logic [10:0] shift_amt;
                logic [52:0] full_mant;  // 1 bit + 52 bits mantissa
                logic [23:0] shifted;
                logic        sub_round, sub_sticky, sub_lsb;
                logic [23:0] sub_rounded;

                exp_f = 8'h00;
                shift_amt = 11'd897 - exp_d;  // 1 to 23
                full_mant = {1'b1, mant_d};   // 53 bits total

                // We need to shift right by shift_amt and round
                // After shift, we take bits [52:30] as the 23-bit subnormal mantissa
                // Round bit is bit 29, sticky is bits 28:0 OR'd together
                if (shift_amt <= 11'd24) begin
                    // Perform the shift
                    shifted = full_mant[52:29] >> shift_amt;

                    // Calculate round and sticky bits
                    // The round bit is at position (29 + shift_amt - 1) in full_mant
                    // Actually, after conceptual shift by shift_amt:
                    // - new bit 29 = old bit (29 + shift_amt) = round bit
                    // - bits below that = sticky
                    sub_round = (full_mant >> (28 + shift_amt)) & 1'b1;
                    sub_sticky = |(full_mant & ((53'b1 << (28 + shift_amt)) - 1));
                    sub_lsb = shifted[0];

                    if (sub_round && (sub_sticky || sub_lsb)) begin
                        sub_rounded = shifted + 1'b1;
                        // Check if rounding caused overflow to normal
                        if (sub_rounded[23]) begin
                            exp_f = 8'h01;  // Becomes smallest normal
                            mant_f = 23'h0;
                        end else begin
                            mant_f = sub_rounded[22:0];
                        end
                    end else begin
                        mant_f = shifted[22:0];
                    end
                end else begin
                    // Shift amount too large, underflow to zero
                    mant_f = 23'h0;
                end
            end
            else if (exp_d > 11'd1150) begin
                exp_f = 8'hFF;
                mant_f = 23'h0;
            end
            else begin
                exp_f = exp_d - 11'd896;
                round_bit = mant_d[28];
                sticky_bit = |mant_d[27:0];
                lsb = mant_d[29];
                if (round_bit && (sticky_bit || lsb)) begin
                    mant_rounded = mant_d[51:29] + 1'b1;
                    if (mant_rounded[23]) begin
                        exp_f = exp_f + 1'b1;
                        mant_f = 23'h0;
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

    // Convert signed i64 to f32 with proper IEEE round-to-nearest-even
    function automatic logic [31:0] i64s_to_f32_bits(input logic [63:0] val);
        logic        sign;
        logic [63:0] abs_val;
        logic [5:0]  leading_one;  // Position of leading 1 (0-63)
        logic [7:0]  exp_f;
        logic [22:0] mant_f;
        logic [63:0] shifted;
        logic        round_bit, sticky_bit, lsb;
        logic [24:0] mant_with_round;  // 25 bits to detect overflow
        int i;

        // Handle zero
        if (val == 64'h0) return 32'h0;

        // Extract sign and absolute value
        sign = val[63];
        abs_val = sign ? -val : val;

        // Find position of leading 1
        leading_one = 0;
        for (i = 63; i >= 0; i = i - 1) begin
            if (abs_val[i]) begin
                leading_one = i[5:0];
                break;
            end
        end

        // If the value fits in 24 bits, no rounding needed
        if (leading_one < 24) begin
            exp_f = leading_one + 8'd127;
            mant_f = (abs_val << (23 - leading_one));
            return {sign, exp_f, mant_f[22:0]};
        end

        // Need to round - shift so bit 23 aligns with leading 1
        // shifted[23] = leading 1, shifted[22:0] = mantissa bits
        // bits below shifted[0] determine rounding
        shifted = abs_val >> (leading_one - 23);

        // Round bit is the bit just below the mantissa
        round_bit = (abs_val >> (leading_one - 24)) & 1'b1;

        // Sticky bit is OR of all bits below round bit
        if (leading_one >= 25) begin
            sticky_bit = |(abs_val & ((64'b1 << (leading_one - 24)) - 1));
        end else begin
            sticky_bit = 1'b0;
        end

        lsb = shifted[0];

        // Round to nearest, ties to even
        if (round_bit && (sticky_bit || lsb)) begin
            mant_with_round = shifted[23:0] + 1'b1;
        end else begin
            mant_with_round = shifted[23:0];
        end

        // Check for mantissa overflow (rounding caused carry into bit 24)
        if (mant_with_round[24]) begin
            exp_f = leading_one + 8'd127 + 1;
            mant_f = mant_with_round[23:1];
        end else begin
            exp_f = leading_one + 8'd127;
            mant_f = mant_with_round[22:0];
        end

        // Check for overflow to infinity
        if (exp_f >= 8'd255) begin
            return {sign, 8'hFF, 23'h0};
        end

        return {sign, exp_f, mant_f};
    endfunction

    // Convert unsigned i64 to f32 with proper IEEE round-to-nearest-even
    function automatic logic [31:0] i64u_to_f32_bits(input logic [63:0] val);
        logic [5:0]  leading_one;
        logic [7:0]  exp_f;
        logic [22:0] mant_f;
        logic [63:0] shifted;
        logic        round_bit, sticky_bit, lsb;
        logic [24:0] mant_with_round;  // 25 bits to detect overflow
        int i;

        // Handle zero
        if (val == 64'h0) return 32'h0;

        // Find position of leading 1
        leading_one = 0;
        for (i = 63; i >= 0; i = i - 1) begin
            if (val[i]) begin
                leading_one = i[5:0];
                break;
            end
        end

        // If the value fits in 24 bits, no rounding needed
        if (leading_one < 24) begin
            exp_f = leading_one + 8'd127;
            mant_f = (val << (23 - leading_one));
            return {1'b0, exp_f, mant_f[22:0]};
        end

        // Need to round
        shifted = val >> (leading_one - 23);
        round_bit = (val >> (leading_one - 24)) & 1'b1;

        if (leading_one >= 25) begin
            sticky_bit = |(val & ((64'b1 << (leading_one - 24)) - 1));
        end else begin
            sticky_bit = 1'b0;
        end

        lsb = shifted[0];

        if (round_bit && (sticky_bit || lsb)) begin
            mant_with_round = shifted[23:0] + 1'b1;
        end else begin
            mant_with_round = shifted[23:0];
        end

        if (mant_with_round[24]) begin
            exp_f = leading_one + 8'd127 + 1;
            mant_f = mant_with_round[23:1];
        end else begin
            exp_f = leading_one + 8'd127;
            mant_f = mant_with_round[22:0];
        end

        if (exp_f >= 8'd255) begin
            return {1'b0, 8'hFF, 23'h0};
        end

        return {1'b0, exp_f, mant_f};
    endfunction

    // Convert unsigned i64 to f64 with proper IEEE round-to-nearest-even
    function automatic logic [63:0] i64u_to_f64_bits(input logic [63:0] val);
        logic [5:0]  leading_one;
        logic [10:0] exp_d;
        logic [51:0] mant_d;
        logic [63:0] shifted;
        logic        round_bit, sticky_bit, lsb;
        logic [53:0] mant_with_round;  // 54 bits to detect overflow
        int i;

        // Handle zero
        if (val == 64'h0) return 64'h0;

        // Find position of leading 1
        leading_one = 0;
        for (i = 63; i >= 0; i = i - 1) begin
            if (val[i]) begin
                leading_one = i[5:0];
                break;
            end
        end

        // If the value fits in 53 bits, no rounding needed
        if (leading_one < 53) begin
            exp_d = {5'b0, leading_one} + 11'd1023;
            mant_d = (val << (52 - leading_one));
            return {1'b0, exp_d, mant_d[51:0]};
        end

        // Need to round (leading_one is 53 to 63)
        shifted = val >> (leading_one - 52);
        round_bit = (val >> (leading_one - 53)) & 1'b1;

        if (leading_one >= 54) begin
            sticky_bit = |(val & ((64'b1 << (leading_one - 53)) - 1));
        end else begin
            sticky_bit = 1'b0;
        end

        lsb = shifted[0];

        if (round_bit && (sticky_bit || lsb)) begin
            mant_with_round = shifted[52:0] + 1'b1;
        end else begin
            mant_with_round = shifted[52:0];
        end

        if (mant_with_round[53]) begin
            exp_d = {5'b0, leading_one} + 11'd1023 + 1;
            mant_d = mant_with_round[52:1];
        end else begin
            exp_d = {5'b0, leading_one} + 11'd1023;
            mant_d = mant_with_round[51:0];
        end

        return {1'b0, exp_d, mant_d};
    endfunction

    // Convert f64 (real) to signed 64-bit integer with truncation toward zero
    // $rtoi only gives 32 bits, so we need to do this manually for large values
    function automatic logic [63:0] f64_to_i64_trunc(input logic [63:0] f64);
        logic        sign;
        logic [10:0] exp;
        logic [51:0] mant;
        logic [63:0] significand;
        int          shift_amt;
        logic [63:0] abs_result;

        sign = f64[63];
        exp = f64[62:52];
        mant = f64[51:0];

        // Zero
        if (exp == 11'h0 && mant == 52'h0) return 64'h0;

        // Get the significand (1.mant for normal, 0.mant for subnormal)
        if (exp == 11'h0) begin
            significand = {12'b0, mant};  // Subnormal
            shift_amt = 1 - 1023;
        end else begin
            significand = {11'b0, 1'b1, mant};  // Normal: 1.mant
            shift_amt = exp - 1023;  // Unbiased exponent
        end

        // Calculate result: significand * 2^(exp-1023-52)
        // significand is 53 bits with binary point after bit 52
        // So actual value = significand * 2^(-52) * 2^(exp-1023) = significand * 2^(exp-1075)
        // Maximum valid shift for 64-bit result is 63 (for -2^63)
        if (shift_amt > 63) begin
            // True overflow - this should have been caught by caller
            abs_result = 64'hFFFFFFFFFFFFFFFF;
        end else if (shift_amt >= 52) begin
            // Shift left (result is large)
            abs_result = significand << (shift_amt - 52);
        end else if (shift_amt >= 0) begin
            // Shift right (result fits, may lose precision)
            abs_result = significand >> (52 - shift_amt);
        end else if (shift_amt > -52) begin
            // Small number, shift right more
            abs_result = significand >> (52 - shift_amt);
        end else begin
            // Very small number, truncates to 0
            abs_result = 64'h0;
        end

        // Apply sign
        if (sign)
            return -abs_result;
        else
            return abs_result;
    endfunction

    always_comb begin
        result = 64'h0;
        trap = TRAP_NONE;

        case (op)
            // i32.wrap_i64 - take low 32 bits
            OP_I32_WRAP_I64: begin
                result = {32'b0, i64_in[31:0]};
            end

            // i32.trunc_f32_s - convert f32 to f64, truncate to i32
            OP_I32_TRUNC_F32_S: begin
                if (f32_is_nan || f32_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    real r;
                    longint li;
                    r = $bitstoreal(f32_to_f64_bits(f32_in));
                    // Valid range after truncation: -2147483648 to 2147483647
                    if (r >= 2147483648.0 || r <= -2147483649.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        li = $rtoi(r);
                        result = {{32{li[31]}}, li[31:0]};
                    end
                end
            end

            // i32.trunc_f32_u
            OP_I32_TRUNC_F32_U: begin
                if (f32_is_nan || f32_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    logic [63:0] f64_bits;
                    real r;
                    logic [63:0] trunc_result;
                    f64_bits = f32_to_f64_bits(f32_in);
                    r = $bitstoreal(f64_bits);
                    if (r >= 4294967296.0 || r <= -1.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        trunc_result = f64_to_i64_trunc(f64_bits);
                        result = {32'b0, trunc_result[31:0]};
                    end
                end
            end

            // i32.trunc_f64_s
            OP_I32_TRUNC_F64_S: begin
                if (f64_is_nan || f64_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    real r;
                    logic [63:0] trunc_result;
                    r = $bitstoreal(f64_in);
                    // Check if truncated value would be out of i32 range
                    // Valid range: -2147483648 to 2147483647 (after truncation toward zero)
                    // So input must be: > -2147483649 and < 2147483648
                    if (r >= 2147483648.0 || r <= -2147483649.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        trunc_result = f64_to_i64_trunc(f64_in);
                        result = {{32{trunc_result[31]}}, trunc_result[31:0]};
                    end
                end
            end

            // i32.trunc_f64_u
            OP_I32_TRUNC_F64_U: begin
                if (f64_is_nan || f64_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    real r;
                    logic [63:0] trunc_result;
                    r = $bitstoreal(f64_in);
                    if (r >= 4294967296.0 || r <= -1.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        trunc_result = f64_to_i64_trunc(f64_in);
                        result = {32'b0, trunc_result[31:0]};
                    end
                end
            end

            // i64.extend_i32_s
            OP_I64_EXTEND_I32_S: begin
                result = {{32{i32_in[31]}}, i32_in};
            end

            // i64.extend_i32_u
            OP_I64_EXTEND_I32_U: begin
                result = {32'b0, i32_in};
            end

            // i64.trunc_f32_s - use bit manipulation for proper 64-bit conversion
            OP_I64_TRUNC_F32_S: begin
                if (f32_is_nan || f32_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    logic [63:0] f64_bits;
                    real r;
                    f64_bits = f32_to_f64_bits(f32_in);
                    r = $bitstoreal(f64_bits);
                    if (r >= 9223372036854775808.0 || r < -9223372036854775808.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        result = f64_to_i64_trunc(f64_bits);
                    end
                end
            end

            // i64.trunc_f32_u
            OP_I64_TRUNC_F32_U: begin
                if (f32_is_nan || f32_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    logic [63:0] f64_bits;
                    real r;
                    f64_bits = f32_to_f64_bits(f32_in);
                    r = $bitstoreal(f64_bits);
                    if (r >= 18446744073709551616.0 || r <= -1.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        result = f64_to_i64_trunc(f64_bits);
                    end
                end
            end

            // i64.trunc_f64_s
            OP_I64_TRUNC_F64_S: begin
                if (f64_is_nan || f64_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    real r;
                    r = $bitstoreal(f64_in);
                    if (r >= 9223372036854775808.0 || r < -9223372036854775808.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        result = f64_to_i64_trunc(f64_in);
                    end
                end
            end

            // i64.trunc_f64_u
            OP_I64_TRUNC_F64_U: begin
                if (f64_is_nan || f64_is_inf) begin
                    trap = TRAP_INVALID_CONV;
                end else begin
                    real r;
                    r = $bitstoreal(f64_in);
                    if (r >= 18446744073709551616.0 || r <= -1.0) begin
                        trap = TRAP_INVALID_CONV;
                    end else begin
                        result = f64_to_i64_trunc(f64_in);
                    end
                end
            end

            // f32.convert_i32_s - convert i32 to f64, then demote to f32
            OP_F32_CONVERT_I32_S: begin
                real r;
                r = $signed(i32_in);
                result = {32'b0, f64_to_f32_bits($realtobits(r))};
            end

            // f32.convert_i32_u
            OP_F32_CONVERT_I32_U: begin
                real r;
                r = {1'b0, i32_in};
                result = {32'b0, f64_to_f32_bits($realtobits(r))};
            end

            // f32.convert_i64_s
            OP_F32_CONVERT_I64_S: begin
                result = {32'b0, i64s_to_f32_bits(i64_in)};
            end

            // f32.convert_i64_u
            OP_F32_CONVERT_I64_U: begin
                result = {32'b0, i64u_to_f32_bits(i64_in)};
            end

            // f32.demote_f64
            OP_F32_DEMOTE_F64: begin
                if (f64_is_nan) begin
                    result = {32'b0, 32'h7FC00000};  // Canonical NaN
                end else begin
                    result = {32'b0, f64_to_f32_bits(f64_in)};
                end
            end

            // f64.convert_i32_s
            OP_F64_CONVERT_I32_S: begin
                real r;
                r = $signed(i32_in);
                result = $realtobits(r);
            end

            // f64.convert_i32_u
            OP_F64_CONVERT_I32_U: begin
                real r;
                r = {1'b0, i32_in};
                result = $realtobits(r);
            end

            // f64.convert_i64_s
            OP_F64_CONVERT_I64_S: begin
                real r;
                r = $signed(i64_in);
                result = $realtobits(r);
            end

            // f64.convert_i64_u
            OP_F64_CONVERT_I64_U: begin
                result = i64u_to_f64_bits(i64_in);
            end

            // f64.promote_f32
            OP_F64_PROMOTE_F32: begin
                if (f32_is_nan) begin
                    result = 64'h7FF8000000000000;  // Canonical NaN
                end else begin
                    result = f32_to_f64_bits(f32_in);
                end
            end

            // Reinterpretations (just copy bits)
            OP_I32_REINTERPRET_F32: begin
                result = {32'b0, f32_in};
            end

            OP_I64_REINTERPRET_F64: begin
                result = f64_in;
            end

            OP_F32_REINTERPRET_I32: begin
                result = {32'b0, i32_in};
            end

            OP_F64_REINTERPRET_I64: begin
                result = i64_in;
            end

            // Sign extensions
            OP_I32_EXTEND8_S: begin
                result = {{56{i32_in[7]}}, i32_in[7:0]};
            end

            OP_I32_EXTEND16_S: begin
                result = {{48{i32_in[15]}}, i32_in[15:0]};
            end

            OP_I64_EXTEND8_S: begin
                result = {{56{i64_in[7]}}, i64_in[7:0]};
            end

            OP_I64_EXTEND16_S: begin
                result = {{48{i64_in[15]}}, i64_in[15:0]};
            end

            OP_I64_EXTEND32_S: begin
                result = {{32{i64_in[31]}}, i64_in[31:0]};
            end

            // Extended opcodes (0xFC prefix) - trunc_sat operations
            OP_PREFIX_FC: begin
                case (sub_op)
                    // i32.trunc_sat_f32_s (0xFC 0x00)
                    8'h00: begin
                        if (f32_is_nan) begin
                            result = 64'h0;
                        end else begin
                            logic [63:0] f64_bits;
                            real r;
                            logic [63:0] trunc_result;
                            f64_bits = f32_to_f64_bits(f32_in);
                            r = $bitstoreal(f64_bits);
                            if (r >= 2147483648.0) begin
                                result = 64'h7FFFFFFF;  // INT32_MAX
                            end else if (r <= -2147483649.0) begin
                                result = 64'hFFFFFFFF80000000;  // INT32_MIN sign-extended
                            end else begin
                                trunc_result = f64_to_i64_trunc(f64_bits);
                                result = {{32{trunc_result[31]}}, trunc_result[31:0]};
                            end
                        end
                    end

                    // i32.trunc_sat_f32_u (0xFC 0x01)
                    8'h01: begin
                        if (f32_is_nan) begin
                            result = 64'h0;
                        end else begin
                            real r;
                            r = $bitstoreal(f32_to_f64_bits(f32_in));
                            if (r >= 4294967296.0) begin
                                result = 64'hFFFFFFFF;  // UINT32_MAX
                            end else if (r <= -1.0) begin
                                result = 64'h0;
                            end else begin
                                result = {32'b0, f64_to_i64_trunc(f32_to_f64_bits(f32_in))[31:0]};
                            end
                        end
                    end

                    // i32.trunc_sat_f64_s (0xFC 0x02)
                    8'h02: begin
                        if (f64_is_nan) begin
                            result = 64'h0;
                        end else begin
                            real r;
                            r = $bitstoreal(f64_in);
                            if (r >= 2147483648.0) begin
                                result = 64'h7FFFFFFF;  // INT32_MAX
                            end else if (r <= -2147483649.0) begin
                                result = 64'hFFFFFFFF80000000;  // INT32_MIN sign-extended
                            end else begin
                                logic [63:0] trunc_result;
                                trunc_result = f64_to_i64_trunc(f64_in);
                                result = {{32{trunc_result[31]}}, trunc_result[31:0]};
                            end
                        end
                    end

                    // i32.trunc_sat_f64_u (0xFC 0x03)
                    8'h03: begin
                        if (f64_is_nan) begin
                            result = 64'h0;
                        end else begin
                            real r;
                            r = $bitstoreal(f64_in);
                            if (r >= 4294967296.0) begin
                                result = 64'hFFFFFFFF;  // UINT32_MAX
                            end else if (r <= -1.0) begin
                                result = 64'h0;
                            end else begin
                                result = {32'b0, f64_to_i64_trunc(f64_in)[31:0]};
                            end
                        end
                    end

                    // i64.trunc_sat_f32_s (0xFC 0x04)
                    8'h04: begin
                        if (f32_is_nan) begin
                            result = 64'h0;
                        end else begin
                            real r;
                            r = $bitstoreal(f32_to_f64_bits(f32_in));
                            if (r >= 9223372036854775808.0) begin
                                result = 64'h7FFFFFFFFFFFFFFF;  // INT64_MAX
                            end else if (r <= -9223372036854775809.0) begin
                                result = 64'h8000000000000000;  // INT64_MIN
                            end else begin
                                result = f64_to_i64_trunc(f32_to_f64_bits(f32_in));
                            end
                        end
                    end

                    // i64.trunc_sat_f32_u (0xFC 0x05)
                    8'h05: begin
                        if (f32_is_nan) begin
                            result = 64'h0;
                        end else begin
                            real r;
                            r = $bitstoreal(f32_to_f64_bits(f32_in));
                            if (r >= 18446744073709551616.0) begin
                                result = 64'hFFFFFFFFFFFFFFFF;  // UINT64_MAX
                            end else if (r <= -1.0) begin
                                result = 64'h0;
                            end else begin
                                result = f64_to_i64_trunc(f32_to_f64_bits(f32_in));
                            end
                        end
                    end

                    // i64.trunc_sat_f64_s (0xFC 0x06)
                    8'h06: begin
                        if (f64_is_nan) begin
                            result = 64'h0;
                        end else begin
                            real r;
                            r = $bitstoreal(f64_in);
                            if (r >= 9223372036854775808.0) begin
                                result = 64'h7FFFFFFFFFFFFFFF;  // INT64_MAX
                            end else if (r <= -9223372036854775809.0) begin
                                result = 64'h8000000000000000;  // INT64_MIN
                            end else begin
                                result = f64_to_i64_trunc(f64_in);
                            end
                        end
                    end

                    // i64.trunc_sat_f64_u (0xFC 0x07)
                    8'h07: begin
                        if (f64_is_nan) begin
                            result = 64'h0;
                        end else begin
                            real r;
                            r = $bitstoreal(f64_in);
                            if (r >= 18446744073709551616.0) begin
                                result = 64'hFFFFFFFFFFFFFFFF;  // UINT64_MAX
                            end else if (r <= -1.0) begin
                                result = 64'h0;
                            end else begin
                                result = f64_to_i64_trunc(f64_in);
                            end
                        end
                    end

                    default: result = 64'h0;
                endcase
            end

            default: result = 64'h0;
        endcase
    end

    assign valid_out = valid_in;

endmodule
