// WebAssembly SIMD (v128) ALU
// Implements all SIMD operations for 128-bit vectors
// Supports: i8x16, i16x8, i32x4, i64x2, f32x4, f64x2 lane types

module wasm_alu_v128
    import wasm_pkg::*;
(
    input  logic         clk,
    input  logic         rst_n,

    // Operation inputs
    input  logic         valid_in,
    input  logic [8:0]   op,           // SIMD sub-opcode (fd_opcode_t)
    input  logic [127:0] operand_a,    // First v128 operand
    input  logic [127:0] operand_b,    // Second v128 operand (or shift count)
    input  logic [127:0] operand_c,    // Third operand for bitselect/shuffle
    input  logic [7:0]   lane_idx,     // Lane index for extract/replace

    // Results
    output logic         valid_out,
    output logic [127:0] result,
    output logic [63:0]  scalar_result, // For extract operations (i32/i64/f32/f64)
    output logic         is_scalar,     // True if result is scalar (extract ops)
    output trap_t        trap
);

    // =========================================================================
    // Lane Access Helpers
    // =========================================================================

    // i8x16 lanes
    wire [7:0] a_i8 [0:15];
    wire [7:0] b_i8 [0:15];
    generate
        for (genvar i = 0; i < 16; i++) begin : gen_i8_lanes
            assign a_i8[i] = operand_a[i*8 +: 8];
            assign b_i8[i] = operand_b[i*8 +: 8];
        end
    endgenerate

    // i16x8 lanes
    wire [15:0] a_i16 [0:7];
    wire [15:0] b_i16 [0:7];
    generate
        for (genvar i = 0; i < 8; i++) begin : gen_i16_lanes
            assign a_i16[i] = operand_a[i*16 +: 16];
            assign b_i16[i] = operand_b[i*16 +: 16];
        end
    endgenerate

    // i32x4 lanes
    wire [31:0] a_i32 [0:3];
    wire [31:0] b_i32 [0:3];
    generate
        for (genvar i = 0; i < 4; i++) begin : gen_i32_lanes
            assign a_i32[i] = operand_a[i*32 +: 32];
            assign b_i32[i] = operand_b[i*32 +: 32];
        end
    endgenerate

    // i64x2 lanes
    wire [63:0] a_i64 [0:1];
    wire [63:0] b_i64 [0:1];
    generate
        for (genvar i = 0; i < 2; i++) begin : gen_i64_lanes
            assign a_i64[i] = operand_a[i*64 +: 64];
            assign b_i64[i] = operand_b[i*64 +: 64];
        end
    endgenerate

    // f32x4 lanes (as bit patterns)
    wire [31:0] a_f32 [0:3];
    wire [31:0] b_f32 [0:3];
    generate
        for (genvar i = 0; i < 4; i++) begin : gen_f32_lanes
            assign a_f32[i] = operand_a[i*32 +: 32];
            assign b_f32[i] = operand_b[i*32 +: 32];
        end
    endgenerate

    // f64x2 lanes (as bit patterns)
    wire [63:0] a_f64 [0:1];
    wire [63:0] b_f64 [0:1];
    generate
        for (genvar i = 0; i < 2; i++) begin : gen_f64_lanes
            assign a_f64[i] = operand_a[i*64 +: 64];
            assign b_f64[i] = operand_b[i*64 +: 64];
        end
    endgenerate

    // =========================================================================
    // Floating-Point Helper Functions
    // =========================================================================

    // IEEE 754 constants
    localparam [31:0] F32_CANONICAL_NAN = 32'h7FC00000;
    localparam [31:0] F32_POS_ZERO = 32'h00000000;
    localparam [31:0] F32_NEG_ZERO = 32'h80000000;
    localparam [31:0] F32_POS_INF  = 32'h7F800000;
    localparam [31:0] F32_NEG_INF  = 32'hFF800000;

    localparam [63:0] F64_CANONICAL_NAN = 64'h7FF8000000000000;
    localparam [63:0] F64_POS_ZERO = 64'h0000000000000000;
    localparam [63:0] F64_NEG_ZERO = 64'h8000000000000000;
    localparam [63:0] F64_POS_INF  = 64'h7FF0000000000000;
    localparam [63:0] F64_NEG_INF  = 64'hFFF0000000000000;

    // f32 special value detection
    function automatic logic f32_is_zero(input logic [31:0] f);
        return (f[30:23] == 8'h00) && (f[22:0] == 23'h0);
    endfunction

    function automatic logic f32_is_inf(input logic [31:0] f);
        return (f[30:23] == 8'hFF) && (f[22:0] == 23'h0);
    endfunction

    function automatic logic f32_is_nan(input logic [31:0] f);
        return (f[30:23] == 8'hFF) && (f[22:0] != 23'h0);
    endfunction

    // f64 special value detection
    function automatic logic f64_is_zero(input logic [63:0] f);
        return (f[62:52] == 11'h000) && (f[51:0] == 52'h0);
    endfunction

    function automatic logic f64_is_inf(input logic [63:0] f);
        return (f[62:52] == 11'h7FF) && (f[51:0] == 52'h0);
    endfunction

    function automatic logic f64_is_nan(input logic [63:0] f);
        return (f[62:52] == 11'h7FF) && (f[51:0] != 52'h0);
    endfunction

    // Convert f32 bits to f64 bits for use with $bitstoreal
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
            // Infinity or NaN
            exp_d = 11'h7FF;
            mant_d = {mant_f, 29'b0};
        end
        else if (exp_f == 8'h00) begin
            if (mant_f == 23'h0) begin
                // Zero
                exp_d = 11'h000;
                mant_d = 52'h0;
            end
            else begin
                // Subnormal f32 - normalize for f64
                shift = 0;
                for (int i = 22; i >= 0; i--) begin
                    if (mant_f[i]) begin
                        shift = i;
                        break;
                    end
                end
                exp_d = 11'd874 + shift;
                if (shift > 0) begin
                    logic [51:0] masked_mant;
                    masked_mant = {29'b0, mant_f} & ((52'b1 << shift) - 1);
                    mant_d = masked_mant << (52 - shift);
                end else begin
                    mant_d = 52'h0;
                end
            end
        end
        else begin
            // Normal number
            exp_d = {3'b0, exp_f} + 11'd896;
            mant_d = {mant_f, 29'b0};
        end

        return {sign_f, exp_d, mant_d};
    endfunction

    // Convert f64 bits to f32 bits with proper rounding
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
                exp_f = 8'h00;
                mant_f = 23'h0;
            end
            else if (exp_d < 11'd897) begin
                // Subnormal f32
                logic [10:0] shift_amt;
                logic [52:0] full_mant;
                logic [23:0] shifted;
                logic        sub_round, sub_sticky, sub_lsb;
                logic [23:0] sub_rounded;

                exp_f = 8'h00;
                shift_amt = 11'd897 - exp_d;
                full_mant = {1'b1, mant_d};

                if (shift_amt <= 11'd24) begin
                    shifted = full_mant[52:29] >> shift_amt;
                    sub_round = (full_mant >> (28 + shift_amt)) & 1'b1;
                    sub_sticky = |(full_mant & ((53'b1 << (28 + shift_amt)) - 1));
                    sub_lsb = shifted[0];

                    if (sub_round && (sub_sticky || sub_lsb)) begin
                        sub_rounded = shifted + 1'b1;
                        if (sub_rounded[23]) begin
                            exp_f = 8'h01;
                            mant_f = 23'h0;
                        end else begin
                            mant_f = sub_rounded[22:0];
                        end
                    end else begin
                        mant_f = shifted[22:0];
                    end
                end else begin
                    mant_f = 23'h0;
                end
            end
            else if (exp_d > 11'd896 + 11'd254) begin
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

    // f32 comparison helpers
    function automatic logic f32_eq(input logic [31:0] a, input logic [31:0] b);
        if (f32_is_nan(a) || f32_is_nan(b)) return 1'b0;
        if (f32_is_zero(a) && f32_is_zero(b)) return 1'b1;
        return a == b;
    endfunction

    function automatic logic f32_lt(input logic [31:0] a, input logic [31:0] b);
        if (f32_is_nan(a) || f32_is_nan(b)) return 1'b0;
        if (f32_is_zero(a) && f32_is_zero(b)) return 1'b0;
        if (!a[31] && !b[31]) return a < b;
        if (a[31] && b[31]) return a > b;
        if (a[31] && !b[31]) return 1'b1;
        return 1'b0;
    endfunction

    function automatic logic f32_gt(input logic [31:0] a, input logic [31:0] b);
        return f32_lt(b, a);
    endfunction

    function automatic logic f32_le(input logic [31:0] a, input logic [31:0] b);
        return f32_lt(a, b) || f32_eq(a, b);
    endfunction

    function automatic logic f32_ge(input logic [31:0] a, input logic [31:0] b);
        return f32_gt(a, b) || f32_eq(a, b);
    endfunction

    // f64 comparison helpers
    function automatic logic f64_eq(input logic [63:0] a, input logic [63:0] b);
        if (f64_is_nan(a) || f64_is_nan(b)) return 1'b0;
        if (f64_is_zero(a) && f64_is_zero(b)) return 1'b1;
        return a == b;
    endfunction

    function automatic logic f64_lt(input logic [63:0] a, input logic [63:0] b);
        if (f64_is_nan(a) || f64_is_nan(b)) return 1'b0;
        if (f64_is_zero(a) && f64_is_zero(b)) return 1'b0;
        if (!a[63] && !b[63]) return a < b;
        if (a[63] && b[63]) return a > b;
        if (a[63] && !b[63]) return 1'b1;
        return 1'b0;
    endfunction

    function automatic logic f64_gt(input logic [63:0] a, input logic [63:0] b);
        return f64_lt(b, a);
    endfunction

    function automatic logic f64_le(input logic [63:0] a, input logic [63:0] b);
        return f64_lt(a, b) || f64_eq(a, b);
    endfunction

    function automatic logic f64_ge(input logic [63:0] a, input logic [63:0] b);
        return f64_gt(a, b) || f64_eq(a, b);
    endfunction

    // =========================================================================
    // Result Assembly
    // =========================================================================
    logic [7:0]  r_i8 [0:15];
    logic [15:0] r_i16 [0:7];
    logic [31:0] r_i32 [0:3];
    logic [63:0] r_i64 [0:1];

    // Pack results into 128-bit
    wire [127:0] result_i8  = {r_i8[15], r_i8[14], r_i8[13], r_i8[12],
                               r_i8[11], r_i8[10], r_i8[9],  r_i8[8],
                               r_i8[7],  r_i8[6],  r_i8[5],  r_i8[4],
                               r_i8[3],  r_i8[2],  r_i8[1],  r_i8[0]};
    wire [127:0] result_i16 = {r_i16[7], r_i16[6], r_i16[5], r_i16[4],
                               r_i16[3], r_i16[2], r_i16[1], r_i16[0]};
    wire [127:0] result_i32 = {r_i32[3], r_i32[2], r_i32[1], r_i32[0]};
    wire [127:0] result_i64 = {r_i64[1], r_i64[0]};

    // =========================================================================
    // Saturating Arithmetic Helpers
    // =========================================================================

    function automatic logic [7:0] sat_add_i8_s(input logic [7:0] a, input logic [7:0] b);
        logic signed [8:0] sum;
        sum = $signed({a[7], a}) + $signed({b[7], b});
        if (sum > 127) return 8'd127;
        else if (sum < -128) return 8'h80;
        else return sum[7:0];
    endfunction

    function automatic logic [7:0] sat_add_i8_u(input logic [7:0] a, input logic [7:0] b);
        logic [8:0] sum;
        sum = {1'b0, a} + {1'b0, b};
        if (sum > 255) return 8'hFF;
        else return sum[7:0];
    endfunction

    function automatic logic [7:0] sat_sub_i8_s(input logic [7:0] a, input logic [7:0] b);
        logic signed [8:0] diff;
        diff = $signed({a[7], a}) - $signed({b[7], b});
        if (diff > 127) return 8'd127;
        else if (diff < -128) return 8'h80;
        else return diff[7:0];
    endfunction

    function automatic logic [7:0] sat_sub_i8_u(input logic [7:0] a, input logic [7:0] b);
        logic signed [8:0] diff;
        diff = {1'b0, a} - {1'b0, b};
        if (diff < 0) return 8'h00;
        else return diff[7:0];
    endfunction

    function automatic logic [15:0] sat_add_i16_s(input logic [15:0] a, input logic [15:0] b);
        logic signed [16:0] sum;
        sum = $signed({a[15], a}) + $signed({b[15], b});
        if (sum > 32767) return 16'd32767;
        else if (sum < -32768) return 16'h8000;
        else return sum[15:0];
    endfunction

    function automatic logic [15:0] sat_add_i16_u(input logic [15:0] a, input logic [15:0] b);
        logic [16:0] sum;
        sum = {1'b0, a} + {1'b0, b};
        if (sum > 65535) return 16'hFFFF;
        else return sum[15:0];
    endfunction

    function automatic logic [15:0] sat_sub_i16_s(input logic [15:0] a, input logic [15:0] b);
        logic signed [16:0] diff;
        diff = $signed({a[15], a}) - $signed({b[15], b});
        if (diff > 32767) return 16'd32767;
        else if (diff < -32768) return 16'h8000;
        else return diff[15:0];
    endfunction

    function automatic logic [15:0] sat_sub_i16_u(input logic [15:0] a, input logic [15:0] b);
        logic signed [16:0] diff;
        diff = {1'b0, a} - {1'b0, b};
        if (diff < 0) return 16'h0000;
        else return diff[15:0];
    endfunction

    // =========================================================================
    // Main ALU Logic
    // =========================================================================
    always_comb begin
        // Default values
        for (int i = 0; i < 16; i++) r_i8[i] = 8'b0;
        for (int i = 0; i < 8; i++) r_i16[i] = 16'b0;
        for (int i = 0; i < 4; i++) r_i32[i] = 32'b0;
        for (int i = 0; i < 2; i++) r_i64[i] = 64'b0;

        result = 128'b0;
        scalar_result = 64'b0;
        is_scalar = 1'b0;
        trap = TRAP_NONE;

        case (op)
            // =================================================================
            // v128 bitwise operations
            // =================================================================
            FD_V128_NOT: begin
                result = ~operand_a;
            end

            FD_V128_AND: begin
                result = operand_a & operand_b;
            end

            FD_V128_ANDNOT: begin
                result = operand_a & ~operand_b;
            end

            FD_V128_OR: begin
                result = operand_a | operand_b;
            end

            FD_V128_XOR: begin
                result = operand_a ^ operand_b;
            end

            FD_V128_BITSELECT: begin
                // result = (a & c) | (b & ~c)
                result = (operand_a & operand_c) | (operand_b & ~operand_c);
            end

            FD_V128_ANY_TRUE: begin
                scalar_result = {63'b0, operand_a != 128'b0};
                is_scalar = 1'b1;
            end

            // =================================================================
            // i8x16 operations
            // =================================================================
            FD_I8X16_SPLAT: begin
                for (int i = 0; i < 16; i++) r_i8[i] = operand_a[7:0];
                result = result_i8;
            end

            FD_I8X16_EXTRACT_LANE_S: begin
                scalar_result = {{56{a_i8[lane_idx[3:0]][7]}}, a_i8[lane_idx[3:0]]};
                is_scalar = 1'b1;
            end

            FD_I8X16_EXTRACT_LANE_U: begin
                scalar_result = {56'b0, a_i8[lane_idx[3:0]]};
                is_scalar = 1'b1;
            end

            FD_I8X16_REPLACE_LANE: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (i == lane_idx[3:0]) ? operand_b[7:0] : a_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_EQ: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] == b_i8[i]) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_NE: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] != b_i8[i]) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_LT_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ($signed(a_i8[i]) < $signed(b_i8[i])) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_LT_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] < b_i8[i]) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_GT_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ($signed(a_i8[i]) > $signed(b_i8[i])) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_GT_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] > b_i8[i]) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_LE_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ($signed(a_i8[i]) <= $signed(b_i8[i])) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_LE_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] <= b_i8[i]) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_GE_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ($signed(a_i8[i]) >= $signed(b_i8[i])) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_GE_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] >= b_i8[i]) ? 8'hFF : 8'h00;
                end
                result = result_i8;
            end

            FD_I8X16_ABS: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = a_i8[i][7] ? (~a_i8[i] + 8'd1) : a_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_NEG: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ~a_i8[i] + 8'd1;
                end
                result = result_i8;
            end

            FD_I8X16_ADD: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = a_i8[i] + b_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_SUB: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = a_i8[i] - b_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_ADD_SAT_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = sat_add_i8_s(a_i8[i], b_i8[i]);
                end
                result = result_i8;
            end

            FD_I8X16_ADD_SAT_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = sat_add_i8_u(a_i8[i], b_i8[i]);
                end
                result = result_i8;
            end

            FD_I8X16_SUB_SAT_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = sat_sub_i8_s(a_i8[i], b_i8[i]);
                end
                result = result_i8;
            end

            FD_I8X16_SUB_SAT_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = sat_sub_i8_u(a_i8[i], b_i8[i]);
                end
                result = result_i8;
            end

            FD_I8X16_MIN_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ($signed(a_i8[i]) < $signed(b_i8[i])) ? a_i8[i] : b_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_MIN_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] < b_i8[i]) ? a_i8[i] : b_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_MAX_S: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ($signed(a_i8[i]) > $signed(b_i8[i])) ? a_i8[i] : b_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_MAX_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = (a_i8[i] > b_i8[i]) ? a_i8[i] : b_i8[i];
                end
                result = result_i8;
            end

            FD_I8X16_AVGR_U: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = ({1'b0, a_i8[i]} + {1'b0, b_i8[i]} + 9'd1) >> 1;
                end
                result = result_i8;
            end

            FD_I8X16_SHL: begin
                logic [2:0] shift;
                shift = operand_b[2:0];  // mod 8
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = a_i8[i] << shift;
                end
                result = result_i8;
            end

            FD_I8X16_SHR_S: begin
                logic [2:0] shift;
                shift = operand_b[2:0];  // mod 8
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = $signed(a_i8[i]) >>> shift;
                end
                result = result_i8;
            end

            FD_I8X16_SHR_U: begin
                logic [2:0] shift;
                shift = operand_b[2:0];  // mod 8
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = a_i8[i] >> shift;
                end
                result = result_i8;
            end

            FD_I8X16_ALL_TRUE: begin
                logic all_nonzero;
                all_nonzero = 1'b1;
                for (int i = 0; i < 16; i++) begin
                    if (a_i8[i] == 8'b0) all_nonzero = 1'b0;
                end
                scalar_result = {63'b0, all_nonzero};
                is_scalar = 1'b1;
            end

            FD_I8X16_BITMASK: begin
                logic [15:0] mask;
                for (int i = 0; i < 16; i++) begin
                    mask[i] = a_i8[i][7];
                end
                scalar_result = {48'b0, mask};
                is_scalar = 1'b1;
            end

            FD_I8X16_POPCNT: begin
                for (int i = 0; i < 16; i++) begin
                    r_i8[i] = a_i8[i][0] + a_i8[i][1] + a_i8[i][2] + a_i8[i][3] +
                              a_i8[i][4] + a_i8[i][5] + a_i8[i][6] + a_i8[i][7];
                end
                result = result_i8;
            end

            FD_I8X16_SWIZZLE: begin
                // i8x16.swizzle: select bytes from operand_a using indices in operand_b
                for (int i = 0; i < 16; i++) begin
                    logic [7:0] idx;
                    idx = b_i8[i];
                    r_i8[i] = (idx < 16) ? a_i8[idx[3:0]] : 8'b0;
                end
                result = result_i8;
            end

            FD_I8X16_SHUFFLE: begin
                // i8x16.shuffle: select bytes from concat(a,b) using indices in operand_c
                logic [7:0] c_i8 [0:15];
                for (int i = 0; i < 16; i++) begin
                    c_i8[i] = operand_c[i*8 +: 8];
                end
                for (int i = 0; i < 16; i++) begin
                    logic [4:0] idx;
                    idx = c_i8[i][4:0];
                    if (idx < 16)
                        r_i8[i] = a_i8[idx[3:0]];
                    else if (idx < 32)
                        r_i8[i] = b_i8[idx[3:0]];
                    else
                        r_i8[i] = 8'b0;
                end
                result = result_i8;
            end

            // =================================================================
            // i16x8 operations
            // =================================================================
            FD_I16X8_SPLAT: begin
                for (int i = 0; i < 8; i++) r_i16[i] = operand_a[15:0];
                result = result_i16;
            end

            FD_I16X8_EXTRACT_LANE_S: begin
                scalar_result = {{48{a_i16[lane_idx[2:0]][15]}}, a_i16[lane_idx[2:0]]};
                is_scalar = 1'b1;
            end

            FD_I16X8_EXTRACT_LANE_U: begin
                scalar_result = {48'b0, a_i16[lane_idx[2:0]]};
                is_scalar = 1'b1;
            end

            FD_I16X8_REPLACE_LANE: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (i == lane_idx[2:0]) ? operand_b[15:0] : a_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_EQ: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] == b_i16[i]) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_NE: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] != b_i16[i]) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_LT_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ($signed(a_i16[i]) < $signed(b_i16[i])) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_LT_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] < b_i16[i]) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_GT_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ($signed(a_i16[i]) > $signed(b_i16[i])) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_GT_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] > b_i16[i]) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_LE_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ($signed(a_i16[i]) <= $signed(b_i16[i])) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_LE_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] <= b_i16[i]) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_GE_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ($signed(a_i16[i]) >= $signed(b_i16[i])) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_GE_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] >= b_i16[i]) ? 16'hFFFF : 16'h0000;
                end
                result = result_i16;
            end

            FD_I16X8_ABS: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = a_i16[i][15] ? (~a_i16[i] + 16'd1) : a_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_NEG: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ~a_i16[i] + 16'd1;
                end
                result = result_i16;
            end

            FD_I16X8_ADD: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = a_i16[i] + b_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_SUB: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = a_i16[i] - b_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_MUL: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = a_i16[i] * b_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_ADD_SAT_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = sat_add_i16_s(a_i16[i], b_i16[i]);
                end
                result = result_i16;
            end

            FD_I16X8_ADD_SAT_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = sat_add_i16_u(a_i16[i], b_i16[i]);
                end
                result = result_i16;
            end

            FD_I16X8_SUB_SAT_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = sat_sub_i16_s(a_i16[i], b_i16[i]);
                end
                result = result_i16;
            end

            FD_I16X8_SUB_SAT_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = sat_sub_i16_u(a_i16[i], b_i16[i]);
                end
                result = result_i16;
            end

            FD_I16X8_MIN_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ($signed(a_i16[i]) < $signed(b_i16[i])) ? a_i16[i] : b_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_MIN_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] < b_i16[i]) ? a_i16[i] : b_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_MAX_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ($signed(a_i16[i]) > $signed(b_i16[i])) ? a_i16[i] : b_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_MAX_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = (a_i16[i] > b_i16[i]) ? a_i16[i] : b_i16[i];
                end
                result = result_i16;
            end

            FD_I16X8_AVGR_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = ({1'b0, a_i16[i]} + {1'b0, b_i16[i]} + 17'd1) >> 1;
                end
                result = result_i16;
            end

            FD_I16X8_SHL: begin
                logic [3:0] shift;
                shift = operand_b[3:0];  // mod 16
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = a_i16[i] << shift;
                end
                result = result_i16;
            end

            FD_I16X8_SHR_S: begin
                logic [3:0] shift;
                shift = operand_b[3:0];  // mod 16
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = $signed(a_i16[i]) >>> shift;
                end
                result = result_i16;
            end

            FD_I16X8_SHR_U: begin
                logic [3:0] shift;
                shift = operand_b[3:0];  // mod 16
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = a_i16[i] >> shift;
                end
                result = result_i16;
            end

            FD_I16X8_ALL_TRUE: begin
                logic all_nonzero;
                all_nonzero = 1'b1;
                for (int i = 0; i < 8; i++) begin
                    if (a_i16[i] == 16'b0) all_nonzero = 1'b0;
                end
                scalar_result = {63'b0, all_nonzero};
                is_scalar = 1'b1;
            end

            FD_I16X8_BITMASK: begin
                logic [7:0] mask;
                for (int i = 0; i < 8; i++) begin
                    mask[i] = a_i16[i][15];
                end
                scalar_result = {56'b0, mask};
                is_scalar = 1'b1;
            end

            // =================================================================
            // i32x4 operations
            // =================================================================
            FD_I32X4_SPLAT: begin
                for (int i = 0; i < 4; i++) r_i32[i] = operand_a[31:0];
                result = result_i32;
            end

            FD_I32X4_EXTRACT_LANE: begin
                scalar_result = {32'b0, a_i32[lane_idx[1:0]]};
                is_scalar = 1'b1;
            end

            FD_I32X4_REPLACE_LANE: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (i == lane_idx[1:0]) ? operand_b[31:0] : a_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_EQ: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] == b_i32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_NE: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] != b_i32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_LT_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = ($signed(a_i32[i]) < $signed(b_i32[i])) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_LT_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] < b_i32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_GT_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = ($signed(a_i32[i]) > $signed(b_i32[i])) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_GT_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] > b_i32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_LE_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = ($signed(a_i32[i]) <= $signed(b_i32[i])) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_LE_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] <= b_i32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_GE_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = ($signed(a_i32[i]) >= $signed(b_i32[i])) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_GE_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] >= b_i32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_I32X4_ABS: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = a_i32[i][31] ? (~a_i32[i] + 32'd1) : a_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_NEG: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = ~a_i32[i] + 32'd1;
                end
                result = result_i32;
            end

            FD_I32X4_ADD: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = a_i32[i] + b_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_SUB: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = a_i32[i] - b_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_MUL: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = a_i32[i] * b_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_MIN_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = ($signed(a_i32[i]) < $signed(b_i32[i])) ? a_i32[i] : b_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_MIN_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] < b_i32[i]) ? a_i32[i] : b_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_MAX_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = ($signed(a_i32[i]) > $signed(b_i32[i])) ? a_i32[i] : b_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_MAX_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (a_i32[i] > b_i32[i]) ? a_i32[i] : b_i32[i];
                end
                result = result_i32;
            end

            FD_I32X4_SHL: begin
                logic [4:0] shift;
                shift = operand_b[4:0];  // mod 32
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = a_i32[i] << shift;
                end
                result = result_i32;
            end

            FD_I32X4_SHR_S: begin
                logic [4:0] shift;
                shift = operand_b[4:0];  // mod 32
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = $signed(a_i32[i]) >>> shift;
                end
                result = result_i32;
            end

            FD_I32X4_SHR_U: begin
                logic [4:0] shift;
                shift = operand_b[4:0];  // mod 32
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = a_i32[i] >> shift;
                end
                result = result_i32;
            end

            FD_I32X4_ALL_TRUE: begin
                logic all_nonzero;
                all_nonzero = 1'b1;
                for (int i = 0; i < 4; i++) begin
                    if (a_i32[i] == 32'b0) all_nonzero = 1'b0;
                end
                scalar_result = {63'b0, all_nonzero};
                is_scalar = 1'b1;
            end

            FD_I32X4_BITMASK: begin
                logic [3:0] mask;
                for (int i = 0; i < 4; i++) begin
                    mask[i] = a_i32[i][31];
                end
                scalar_result = {60'b0, mask};
                is_scalar = 1'b1;
            end

            // =================================================================
            // i64x2 operations
            // =================================================================
            FD_I64X2_SPLAT: begin
                for (int i = 0; i < 2; i++) r_i64[i] = operand_a[63:0];
                result = result_i64;
            end

            FD_I64X2_EXTRACT_LANE: begin
                scalar_result = a_i64[lane_idx[0]];
                is_scalar = 1'b1;
            end

            FD_I64X2_REPLACE_LANE: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = (i == lane_idx[0]) ? operand_b[63:0] : a_i64[i];
                end
                result = result_i64;
            end

            FD_I64X2_EQ: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = (a_i64[i] == b_i64[i]) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_I64X2_NE: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = (a_i64[i] != b_i64[i]) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_I64X2_LT_S: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = ($signed(a_i64[i]) < $signed(b_i64[i])) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_I64X2_GT_S: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = ($signed(a_i64[i]) > $signed(b_i64[i])) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_I64X2_LE_S: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = ($signed(a_i64[i]) <= $signed(b_i64[i])) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_I64X2_GE_S: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = ($signed(a_i64[i]) >= $signed(b_i64[i])) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_I64X2_ABS: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = a_i64[i][63] ? (~a_i64[i] + 64'd1) : a_i64[i];
                end
                result = result_i64;
            end

            FD_I64X2_NEG: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = ~a_i64[i] + 64'd1;
                end
                result = result_i64;
            end

            FD_I64X2_ADD: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = a_i64[i] + b_i64[i];
                end
                result = result_i64;
            end

            FD_I64X2_SUB: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = a_i64[i] - b_i64[i];
                end
                result = result_i64;
            end

            FD_I64X2_MUL: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = a_i64[i] * b_i64[i];
                end
                result = result_i64;
            end

            FD_I64X2_SHL: begin
                logic [5:0] shift;
                shift = operand_b[5:0];  // mod 64
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = a_i64[i] << shift;
                end
                result = result_i64;
            end

            FD_I64X2_SHR_S: begin
                logic [5:0] shift;
                shift = operand_b[5:0];  // mod 64
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = $signed(a_i64[i]) >>> shift;
                end
                result = result_i64;
            end

            FD_I64X2_SHR_U: begin
                logic [5:0] shift;
                shift = operand_b[5:0];  // mod 64
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = a_i64[i] >> shift;
                end
                result = result_i64;
            end

            FD_I64X2_ALL_TRUE: begin
                logic all_nonzero;
                all_nonzero = 1'b1;
                for (int i = 0; i < 2; i++) begin
                    if (a_i64[i] == 64'b0) all_nonzero = 1'b0;
                end
                scalar_result = {63'b0, all_nonzero};
                is_scalar = 1'b1;
            end

            FD_I64X2_BITMASK: begin
                logic [1:0] mask;
                for (int i = 0; i < 2; i++) begin
                    mask[i] = a_i64[i][63];
                end
                scalar_result = {62'b0, mask};
                is_scalar = 1'b1;
            end

            // =================================================================
            // f32x4 extract/replace (as bit patterns)
            // =================================================================
            FD_F32X4_SPLAT: begin
                for (int i = 0; i < 4; i++) r_i32[i] = operand_a[31:0];
                result = result_i32;
            end

            FD_F32X4_EXTRACT_LANE: begin
                scalar_result = {32'b0, a_f32[lane_idx[1:0]]};
                is_scalar = 1'b1;
            end

            FD_F32X4_REPLACE_LANE: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = (i == lane_idx[1:0]) ? operand_b[31:0] : a_f32[i];
                end
                result = result_i32;
            end

            // =================================================================
            // f64x2 extract/replace (as bit patterns)
            // =================================================================
            FD_F64X2_SPLAT: begin
                for (int i = 0; i < 2; i++) r_i64[i] = operand_a[63:0];
                result = result_i64;
            end

            FD_F64X2_EXTRACT_LANE: begin
                scalar_result = a_f64[lane_idx[0]];
                is_scalar = 1'b1;
            end

            FD_F64X2_REPLACE_LANE: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = (i == lane_idx[0]) ? operand_b[63:0] : a_f64[i];
                end
                result = result_i64;
            end

            // =================================================================
            // f32x4 comparisons
            // =================================================================
            FD_F32X4_EQ: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = f32_eq(a_f32[i], b_f32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_F32X4_NE: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = f32_eq(a_f32[i], b_f32[i]) ? 32'h00000000 : 32'hFFFFFFFF;
                end
                result = result_i32;
            end

            FD_F32X4_LT: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = f32_lt(a_f32[i], b_f32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_F32X4_GT: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = f32_gt(a_f32[i], b_f32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_F32X4_LE: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = f32_le(a_f32[i], b_f32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            FD_F32X4_GE: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = f32_ge(a_f32[i], b_f32[i]) ? 32'hFFFFFFFF : 32'h00000000;
                end
                result = result_i32;
            end

            // =================================================================
            // f64x2 comparisons
            // =================================================================
            FD_F64X2_EQ: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = f64_eq(a_f64[i], b_f64[i]) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_F64X2_NE: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = f64_eq(a_f64[i], b_f64[i]) ? 64'h0000000000000000 : 64'hFFFFFFFFFFFFFFFF;
                end
                result = result_i64;
            end

            FD_F64X2_LT: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = f64_lt(a_f64[i], b_f64[i]) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_F64X2_GT: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = f64_gt(a_f64[i], b_f64[i]) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_F64X2_LE: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = f64_le(a_f64[i], b_f64[i]) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            FD_F64X2_GE: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = f64_ge(a_f64[i], b_f64[i]) ? 64'hFFFFFFFFFFFFFFFF : 64'h0000000000000000;
                end
                result = result_i64;
            end

            // =================================================================
            // f32x4 unary arithmetic
            // =================================================================
            FD_F32X4_ABS: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = {1'b0, a_f32[i][30:0]};
                end
                result = result_i32;
            end

            FD_F32X4_NEG: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = {~a_f32[i][31], a_f32[i][30:0]};
                end
                result = result_i32;
            end

            FD_F32X4_SQRT: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (a_f32[i][31] && !f32_is_zero(a_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;  // sqrt of negative
                    end
                    else if (f32_is_inf(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else if (f32_is_zero(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rr = $sqrt(ra);
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            // =================================================================
            // f32x4 binary arithmetic
            // =================================================================
            FD_F32X4_ADD: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) && f32_is_inf(b_f32[i]) && (a_f32[i][31] != b_f32[i][31])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else if (f32_is_inf(b_f32[i])) begin
                        r_i32[i] = b_f32[i];
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        rr = ra + rb;
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            FD_F32X4_SUB: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) && f32_is_inf(b_f32[i]) && (a_f32[i][31] == b_f32[i][31])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else if (f32_is_inf(b_f32[i])) begin
                        r_i32[i] = {~b_f32[i][31], b_f32[i][30:0]};
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        rr = ra - rb;
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            FD_F32X4_MUL: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if ((f32_is_inf(a_f32[i]) && f32_is_zero(b_f32[i])) ||
                             (f32_is_zero(a_f32[i]) && f32_is_inf(b_f32[i]))) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) || f32_is_inf(b_f32[i])) begin
                        r_i32[i] = {a_f32[i][31] ^ b_f32[i][31], 8'hFF, 23'h0};
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        rr = ra * rb;
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            FD_F32X4_DIV: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) && f32_is_inf(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_zero(a_f32[i]) && f32_is_zero(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_zero(b_f32[i])) begin
                        r_i32[i] = {a_f32[i][31] ^ b_f32[i][31], 8'hFF, 23'h0};
                    end
                    else if (f32_is_inf(a_f32[i])) begin
                        r_i32[i] = {a_f32[i][31] ^ b_f32[i][31], 8'hFF, 23'h0};
                    end
                    else if (f32_is_inf(b_f32[i])) begin
                        r_i32[i] = {a_f32[i][31] ^ b_f32[i][31], 31'h0};
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        rr = ra / rb;
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            FD_F32X4_MIN: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_zero(a_f32[i]) && f32_is_zero(b_f32[i])) begin
                        r_i32[i] = a_f32[i][31] ? a_f32[i] : b_f32[i];  // -0 < +0
                    end
                    else begin
                        real ra, rb;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        r_i32[i] = (ra < rb) ? a_f32[i] : b_f32[i];
                    end
                end
                result = result_i32;
            end

            FD_F32X4_MAX: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_zero(a_f32[i]) && f32_is_zero(b_f32[i])) begin
                        r_i32[i] = a_f32[i][31] ? b_f32[i] : a_f32[i];  // +0 > -0
                    end
                    else begin
                        real ra, rb;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        r_i32[i] = (ra > rb) ? a_f32[i] : b_f32[i];
                    end
                end
                result = result_i32;
            end

            // pmin/pmax: x86-style comparison, returns NaN if either operand is NaN
            FD_F32X4_PMIN: begin
                for (int i = 0; i < 4; i++) begin
                    // pmin returns b if b < a, else a (including NaN propagation)
                    if (f32_lt(b_f32[i], a_f32[i])) begin
                        r_i32[i] = b_f32[i];
                    end
                    else begin
                        r_i32[i] = a_f32[i];
                    end
                end
                result = result_i32;
            end

            FD_F32X4_PMAX: begin
                for (int i = 0; i < 4; i++) begin
                    // pmax returns b if a < b, else a (including NaN propagation)
                    if (f32_lt(a_f32[i], b_f32[i])) begin
                        r_i32[i] = b_f32[i];
                    end
                    else begin
                        r_i32[i] = a_f32[i];
                    end
                end
                result = result_i32;
            end

            // =================================================================
            // f32x4 rounding
            // =================================================================
            FD_F32X4_CEIL: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) || f32_is_zero(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rr = $ceil(ra);
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            FD_F32X4_FLOOR: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) || f32_is_zero(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rr = $floor(ra);
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            FD_F32X4_TRUNC: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) || f32_is_zero(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rr = (ra >= 0) ? $floor(ra) : $ceil(ra);
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            FD_F32X4_NEAREST: begin
                for (int i = 0; i < 4; i++) begin
                    logic [7:0] exp_a_f32;
                    exp_a_f32 = a_f32[i][30:23];
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else if (f32_is_inf(a_f32[i]) || f32_is_zero(a_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end
                    else if (exp_a_f32 >= 8'd150) begin
                        // Already integer
                        r_i32[i] = a_f32[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        if (ra >= 0.0) begin
                            rr = $floor(ra + 0.5);
                            if (ra - $floor(ra) == 0.5) begin
                                if ($rtoi(rr) % 2 != 0) rr = rr - 1.0;
                            end
                        end
                        else begin
                            rr = $ceil(ra - 0.5);
                            if ($ceil(ra) - ra == 0.5) begin
                                if ($rtoi(rr) % 2 != 0) rr = rr + 1.0;
                            end
                        end
                        if (rr == 0.0 && a_f32[i][31])
                            r_i32[i] = F32_NEG_ZERO;
                        else
                            r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            // =================================================================
            // f64x2 unary arithmetic
            // =================================================================
            FD_F64X2_ABS: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = {1'b0, a_f64[i][62:0]};
                end
                result = result_i64;
            end

            FD_F64X2_NEG: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = {~a_f64[i][63], a_f64[i][62:0]};
                end
                result = result_i64;
            end

            FD_F64X2_SQRT: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (a_f64[i][63] && !f64_is_zero(a_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;  // sqrt of negative
                    end
                    else if (f64_is_inf(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else if (f64_is_zero(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rr = $sqrt(ra);
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            // =================================================================
            // f64x2 binary arithmetic
            // =================================================================
            FD_F64X2_ADD: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) && f64_is_inf(b_f64[i]) && (a_f64[i][63] != b_f64[i][63])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else if (f64_is_inf(b_f64[i])) begin
                        r_i64[i] = b_f64[i];
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        rr = ra + rb;
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            FD_F64X2_SUB: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) && f64_is_inf(b_f64[i]) && (a_f64[i][63] == b_f64[i][63])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else if (f64_is_inf(b_f64[i])) begin
                        r_i64[i] = {~b_f64[i][63], b_f64[i][62:0]};
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        rr = ra - rb;
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            FD_F64X2_MUL: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if ((f64_is_inf(a_f64[i]) && f64_is_zero(b_f64[i])) ||
                             (f64_is_zero(a_f64[i]) && f64_is_inf(b_f64[i]))) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) || f64_is_inf(b_f64[i])) begin
                        r_i64[i] = {a_f64[i][63] ^ b_f64[i][63], 11'h7FF, 52'h0};
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        rr = ra * rb;
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            FD_F64X2_DIV: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) && f64_is_inf(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_zero(a_f64[i]) && f64_is_zero(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_zero(b_f64[i])) begin
                        r_i64[i] = {a_f64[i][63] ^ b_f64[i][63], 11'h7FF, 52'h0};
                    end
                    else if (f64_is_inf(a_f64[i])) begin
                        r_i64[i] = {a_f64[i][63] ^ b_f64[i][63], 11'h7FF, 52'h0};
                    end
                    else if (f64_is_inf(b_f64[i])) begin
                        r_i64[i] = {a_f64[i][63] ^ b_f64[i][63], 63'h0};
                    end
                    else begin
                        real ra, rb, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        rr = ra / rb;
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            FD_F64X2_MIN: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_zero(a_f64[i]) && f64_is_zero(b_f64[i])) begin
                        r_i64[i] = a_f64[i][63] ? a_f64[i] : b_f64[i];  // -0 < +0
                    end
                    else begin
                        real ra, rb;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        r_i64[i] = (ra < rb) ? a_f64[i] : b_f64[i];
                    end
                end
                result = result_i64;
            end

            FD_F64X2_MAX: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_zero(a_f64[i]) && f64_is_zero(b_f64[i])) begin
                        r_i64[i] = a_f64[i][63] ? b_f64[i] : a_f64[i];  // +0 > -0
                    end
                    else begin
                        real ra, rb;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        r_i64[i] = (ra > rb) ? a_f64[i] : b_f64[i];
                    end
                end
                result = result_i64;
            end

            FD_F64X2_PMIN: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_lt(b_f64[i], a_f64[i])) begin
                        r_i64[i] = b_f64[i];
                    end
                    else begin
                        r_i64[i] = a_f64[i];
                    end
                end
                result = result_i64;
            end

            FD_F64X2_PMAX: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_lt(a_f64[i], b_f64[i])) begin
                        r_i64[i] = b_f64[i];
                    end
                    else begin
                        r_i64[i] = a_f64[i];
                    end
                end
                result = result_i64;
            end

            // =================================================================
            // f64x2 rounding
            // =================================================================
            FD_F64X2_CEIL: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) || f64_is_zero(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rr = $ceil(ra);
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            FD_F64X2_FLOOR: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) || f64_is_zero(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rr = $floor(ra);
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            FD_F64X2_TRUNC: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) || f64_is_zero(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else begin
                        real ra, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rr = (ra >= 0) ? $floor(ra) : $ceil(ra);
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            FD_F64X2_NEAREST: begin
                for (int i = 0; i < 2; i++) begin
                    logic [10:0] exp_a_f64;
                    exp_a_f64 = a_f64[i][62:52];
                    if (f64_is_nan(a_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else if (f64_is_inf(a_f64[i]) || f64_is_zero(a_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end
                    else if (exp_a_f64 >= 11'd1075) begin
                        // Already integer
                        r_i64[i] = a_f64[i];
                    end
                    else begin
                        real ra, rr, frac;
                        ra = $bitstoreal(a_f64[i]);
                        if (ra >= 0.0) begin
                            frac = ra - $floor(ra);
                            if (frac < 0.5) begin
                                rr = $floor(ra);
                            end else if (frac > 0.5) begin
                                rr = $floor(ra) + 1.0;
                            end else begin
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
                                rr = $ceil(ra);
                                if ($rtoi(rr) % 2 != 0) rr = rr - 1.0;
                            end
                        end
                        if (rr == 0.0 && a_f64[i][63])
                            r_i64[i] = F64_NEG_ZERO;
                        else
                            r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            // =================================================================
            // Float-to-integer conversions (saturating)
            // =================================================================
            FD_I32X4_TRUNC_SAT_F32X4_S: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = 32'h00000000;
                    end
                    else begin
                        real ra;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        if (ra >= 2147483647.0) begin
                            r_i32[i] = 32'h7FFFFFFF;  // INT32_MAX
                        end
                        else if (ra <= -2147483648.0) begin
                            r_i32[i] = 32'h80000000;  // INT32_MIN
                        end
                        else begin
                            r_i32[i] = $rtoi(ra);
                        end
                    end
                end
                result = result_i32;
            end

            FD_I32X4_TRUNC_SAT_F32X4_U: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = 32'h00000000;
                    end
                    else begin
                        real ra;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        if (ra >= 4294967296.0) begin
                            r_i32[i] = 32'hFFFFFFFF;  // UINT32_MAX (saturate)
                        end
                        else if (ra < 0.0) begin
                            r_i32[i] = 32'h00000000;  // saturate negative to 0
                        end
                        else begin
                            // Use $floor for truncation towards zero (for positive values)
                            longint li;
                            li = longint'($floor(ra));
                            r_i32[i] = li[31:0];
                        end
                    end
                end
                result = result_i32;
            end

            FD_I32X4_TRUNC_SAT_F64X2_S_ZERO: begin
                // Convert two f64 to two i32, lower half; upper half is zero
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i32[i] = 32'h00000000;
                    end
                    else begin
                        real ra;
                        ra = $bitstoreal(a_f64[i]);
                        if (ra >= 2147483647.0) begin
                            r_i32[i] = 32'h7FFFFFFF;
                        end
                        else if (ra <= -2147483648.0) begin
                            r_i32[i] = 32'h80000000;
                        end
                        else begin
                            r_i32[i] = $rtoi(ra);
                        end
                    end
                end
                r_i32[2] = 32'h0;
                r_i32[3] = 32'h0;
                result = result_i32;
            end

            FD_I32X4_TRUNC_SAT_F64X2_U_ZERO: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i32[i] = 32'h00000000;
                    end
                    else begin
                        real ra;
                        ra = $bitstoreal(a_f64[i]);
                        if (ra >= 4294967296.0) begin
                            r_i32[i] = 32'hFFFFFFFF;  // UINT32_MAX (saturate)
                        end
                        else if (ra < 0.0) begin
                            r_i32[i] = 32'h00000000;  // saturate negative to 0
                        end
                        else begin
                            // Use $floor for truncation towards zero (for positive values)
                            longint li;
                            li = longint'($floor(ra));
                            r_i32[i] = li[31:0];
                        end
                    end
                end
                r_i32[2] = 32'h0;
                r_i32[3] = 32'h0;
                result = result_i32;
            end

            // =================================================================
            // Integer-to-float conversions
            // =================================================================
            FD_F32X4_CONVERT_I32X4_S: begin
                for (int i = 0; i < 4; i++) begin
                    real rr;
                    rr = $itor($signed(a_i32[i]));
                    r_i32[i] = f64_to_f32_bits($realtobits(rr));
                end
                result = result_i32;
            end

            FD_F32X4_CONVERT_I32X4_U: begin
                for (int i = 0; i < 4; i++) begin
                    real rr;
                    rr = $itor({1'b0, a_i32[i]});
                    r_i32[i] = f64_to_f32_bits($realtobits(rr));
                end
                result = result_i32;
            end

            FD_F64X2_CONVERT_LOW_I32X4_S: begin
                // Convert lower two i32 to f64
                for (int i = 0; i < 2; i++) begin
                    real rr;
                    rr = $itor($signed(a_i32[i]));
                    r_i64[i] = $realtobits(rr);
                end
                result = result_i64;
            end

            FD_F64X2_CONVERT_LOW_I32X4_U: begin
                for (int i = 0; i < 2; i++) begin
                    real rr;
                    rr = $itor({1'b0, a_i32[i]});
                    r_i64[i] = $realtobits(rr);
                end
                result = result_i64;
            end

            // =================================================================
            // Float type conversions
            // =================================================================
            FD_F32X4_DEMOTE_F64X2_ZERO: begin
                // Demote two f64 to f32, store in lower two lanes, zero upper two
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end
                    else begin
                        r_i32[i] = f64_to_f32_bits(a_f64[i]);
                    end
                end
                r_i32[2] = 32'h0;
                r_i32[3] = 32'h0;
                result = result_i32;
            end

            FD_F64X2_PROMOTE_LOW_F32X4: begin
                // Promote lower two f32 to f64
                for (int i = 0; i < 2; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end
                    else begin
                        r_i64[i] = f32_to_f64_bits(a_f32[i]);
                    end
                end
                result = result_i64;
            end

            // =================================================================
            // Integer narrow operations
            // =================================================================

            // i8x16 <- i16x8 narrow (signed saturation)
            FD_I8X16_NARROW_I16X8_S: begin
                // operand_a = low half input, operand_b = high half input
                // Result: [b saturated to i8] [a saturated to i8]
                for (int i = 0; i < 8; i++) begin
                    logic signed [15:0] val;
                    val = $signed(a_i16[i]);
                    if (val > 127) r_i8[i] = 8'd127;
                    else if (val < -128) r_i8[i] = 8'h80;
                    else r_i8[i] = val[7:0];
                end
                for (int i = 0; i < 8; i++) begin
                    logic signed [15:0] val;
                    val = $signed(b_i16[i]);
                    if (val > 127) r_i8[i+8] = 8'd127;
                    else if (val < -128) r_i8[i+8] = 8'h80;
                    else r_i8[i+8] = val[7:0];
                end
                result = result_i8;
            end

            // i8x16 <- i16x8 narrow (unsigned saturation)
            FD_I8X16_NARROW_I16X8_U: begin
                for (int i = 0; i < 8; i++) begin
                    logic signed [15:0] val;
                    val = $signed(a_i16[i]);
                    if (val > 255) r_i8[i] = 8'hFF;
                    else if (val < 0) r_i8[i] = 8'h00;
                    else r_i8[i] = val[7:0];
                end
                for (int i = 0; i < 8; i++) begin
                    logic signed [15:0] val;
                    val = $signed(b_i16[i]);
                    if (val > 255) r_i8[i+8] = 8'hFF;
                    else if (val < 0) r_i8[i+8] = 8'h00;
                    else r_i8[i+8] = val[7:0];
                end
                result = result_i8;
            end

            // i16x8 <- i32x4 narrow (signed saturation)
            FD_I16X8_NARROW_I32X4_S: begin
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] val;
                    val = $signed(a_i32[i]);
                    if (val > 32767) r_i16[i] = 16'd32767;
                    else if (val < -32768) r_i16[i] = 16'h8000;
                    else r_i16[i] = val[15:0];
                end
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] val;
                    val = $signed(b_i32[i]);
                    if (val > 32767) r_i16[i+4] = 16'd32767;
                    else if (val < -32768) r_i16[i+4] = 16'h8000;
                    else r_i16[i+4] = val[15:0];
                end
                result = result_i16;
            end

            // i16x8 <- i32x4 narrow (unsigned saturation)
            FD_I16X8_NARROW_I32X4_U: begin
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] val;
                    val = $signed(a_i32[i]);
                    if (val > 65535) r_i16[i] = 16'hFFFF;
                    else if (val < 0) r_i16[i] = 16'h0000;
                    else r_i16[i] = val[15:0];
                end
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] val;
                    val = $signed(b_i32[i]);
                    if (val > 65535) r_i16[i+4] = 16'hFFFF;
                    else if (val < 0) r_i16[i+4] = 16'h0000;
                    else r_i16[i+4] = val[15:0];
                end
                result = result_i16;
            end

            // =================================================================
            // Extended pairwise addition
            // =================================================================

            // i16x8 <- i8x16 extadd_pairwise (signed)
            FD_I16X8_EXTADD_PAIRWISE_I8X16_S: begin
                for (int i = 0; i < 8; i++) begin
                    logic signed [8:0] a_ext, b_ext;
                    a_ext = $signed(a_i8[i*2]);
                    b_ext = $signed(a_i8[i*2 + 1]);
                    r_i16[i] = a_ext + b_ext;
                end
                result = result_i16;
            end

            // i16x8 <- i8x16 extadd_pairwise (unsigned)
            FD_I16X8_EXTADD_PAIRWISE_I8X16_U: begin
                for (int i = 0; i < 8; i++) begin
                    logic [8:0] a_ext, b_ext;
                    a_ext = {1'b0, a_i8[i*2]};
                    b_ext = {1'b0, a_i8[i*2 + 1]};
                    r_i16[i] = a_ext + b_ext;
                end
                result = result_i16;
            end

            // i32x4 <- i16x8 extadd_pairwise (signed)
            FD_I32X4_EXTADD_PAIRWISE_I16X8_S: begin
                for (int i = 0; i < 4; i++) begin
                    logic signed [16:0] a_ext, b_ext;
                    a_ext = $signed(a_i16[i*2]);
                    b_ext = $signed(a_i16[i*2 + 1]);
                    r_i32[i] = a_ext + b_ext;
                end
                result = result_i32;
            end

            // i32x4 <- i16x8 extadd_pairwise (unsigned)
            FD_I32X4_EXTADD_PAIRWISE_I16X8_U: begin
                for (int i = 0; i < 4; i++) begin
                    logic [16:0] a_ext, b_ext;
                    a_ext = {1'b0, a_i16[i*2]};
                    b_ext = {1'b0, a_i16[i*2 + 1]};
                    r_i32[i] = a_ext + b_ext;
                end
                result = result_i32;
            end

            // =================================================================
            // Q15 saturating rounding multiply
            // =================================================================

            // i16x8.q15mulr_sat_s: multiply, shift right by 15, round, saturate
            FD_I16X8_Q15MULR_SAT_S: begin
                for (int i = 0; i < 8; i++) begin
                    logic signed [31:0] prod;
                    logic signed [31:0] rounded;
                    prod = $signed(a_i16[i]) * $signed(b_i16[i]);
                    // Round by adding 0x4000 before shifting (use signed constant to preserve sign)
                    rounded = (prod + 32'sd16384) >>> 15;
                    // Saturate to i16 range
                    if (rounded > 32767) r_i16[i] = 16'd32767;
                    else if (rounded < -32768) r_i16[i] = 16'h8000;
                    else r_i16[i] = rounded[15:0];
                end
                result = result_i16;
            end

            // =================================================================
            // Dot product
            // =================================================================

            // i32x4.dot_i16x8_s: pairwise multiply and add
            FD_I32X4_DOT_I16X8_S: begin
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] prod1, prod2;
                    prod1 = $signed(a_i16[i*2]) * $signed(b_i16[i*2]);
                    prod2 = $signed(a_i16[i*2 + 1]) * $signed(b_i16[i*2 + 1]);
                    r_i32[i] = prod1 + prod2;
                end
                result = result_i32;
            end

            // =================================================================
            // Integer extend operations
            // =================================================================

            // i16x8 <- i8x16 extend (low 8 bytes, signed)
            FD_I16X8_EXTEND_LOW_I8X16_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = {{8{a_i8[i][7]}}, a_i8[i]};  // Sign extend
                end
                result = result_i16;
            end

            // i16x8 <- i8x16 extend (high 8 bytes, signed)
            FD_I16X8_EXTEND_HIGH_I8X16_S: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = {{8{a_i8[i+8][7]}}, a_i8[i+8]};  // Sign extend
                end
                result = result_i16;
            end

            // i16x8 <- i8x16 extend (low 8 bytes, unsigned)
            FD_I16X8_EXTEND_LOW_I8X16_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = {8'b0, a_i8[i]};  // Zero extend
                end
                result = result_i16;
            end

            // i16x8 <- i8x16 extend (high 8 bytes, unsigned)
            FD_I16X8_EXTEND_HIGH_I8X16_U: begin
                for (int i = 0; i < 8; i++) begin
                    r_i16[i] = {8'b0, a_i8[i+8]};  // Zero extend
                end
                result = result_i16;
            end

            // i32x4 <- i16x8 extend (low 4 words, signed)
            FD_I32X4_EXTEND_LOW_I16X8_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = {{16{a_i16[i][15]}}, a_i16[i]};  // Sign extend
                end
                result = result_i32;
            end

            // i32x4 <- i16x8 extend (high 4 words, signed)
            FD_I32X4_EXTEND_HIGH_I16X8_S: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = {{16{a_i16[i+4][15]}}, a_i16[i+4]};  // Sign extend
                end
                result = result_i32;
            end

            // i32x4 <- i16x8 extend (low 4 words, unsigned)
            FD_I32X4_EXTEND_LOW_I16X8_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = {16'b0, a_i16[i]};  // Zero extend
                end
                result = result_i32;
            end

            // i32x4 <- i16x8 extend (high 4 words, unsigned)
            FD_I32X4_EXTEND_HIGH_I16X8_U: begin
                for (int i = 0; i < 4; i++) begin
                    r_i32[i] = {16'b0, a_i16[i+4]};  // Zero extend
                end
                result = result_i32;
            end

            // i64x2 <- i32x4 extend (low 2 dwords, signed)
            FD_I64X2_EXTEND_LOW_I32X4_S: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = {{32{a_i32[i][31]}}, a_i32[i]};  // Sign extend
                end
                result = result_i64;
            end

            // i64x2 <- i32x4 extend (high 2 dwords, signed)
            FD_I64X2_EXTEND_HIGH_I32X4_S: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = {{32{a_i32[i+2][31]}}, a_i32[i+2]};  // Sign extend
                end
                result = result_i64;
            end

            // i64x2 <- i32x4 extend (low 2 dwords, unsigned)
            FD_I64X2_EXTEND_LOW_I32X4_U: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = {32'b0, a_i32[i]};  // Zero extend
                end
                result = result_i64;
            end

            // i64x2 <- i32x4 extend (high 2 dwords, unsigned)
            FD_I64X2_EXTEND_HIGH_I32X4_U: begin
                for (int i = 0; i < 2; i++) begin
                    r_i64[i] = {32'b0, a_i32[i+2]};  // Zero extend
                end
                result = result_i64;
            end

            // =================================================================
            // Integer extended multiply operations
            // =================================================================

            // i16x8 <- i8x16 extmul (low 8 bytes, signed)
            FD_I16X8_EXTMUL_LOW_I8X16_S: begin
                for (int i = 0; i < 8; i++) begin
                    logic signed [15:0] a_ext, b_ext;
                    a_ext = $signed(a_i8[i]);
                    b_ext = $signed(b_i8[i]);
                    r_i16[i] = a_ext * b_ext;
                end
                result = result_i16;
            end

            // i16x8 <- i8x16 extmul (high 8 bytes, signed)
            FD_I16X8_EXTMUL_HIGH_I8X16_S: begin
                for (int i = 0; i < 8; i++) begin
                    logic signed [15:0] a_ext, b_ext;
                    a_ext = $signed(a_i8[i+8]);
                    b_ext = $signed(b_i8[i+8]);
                    r_i16[i] = a_ext * b_ext;
                end
                result = result_i16;
            end

            // i16x8 <- i8x16 extmul (low 8 bytes, unsigned)
            FD_I16X8_EXTMUL_LOW_I8X16_U: begin
                for (int i = 0; i < 8; i++) begin
                    logic [15:0] a_ext, b_ext;
                    a_ext = {8'b0, a_i8[i]};
                    b_ext = {8'b0, b_i8[i]};
                    r_i16[i] = a_ext * b_ext;
                end
                result = result_i16;
            end

            // i16x8 <- i8x16 extmul (high 8 bytes, unsigned)
            FD_I16X8_EXTMUL_HIGH_I8X16_U: begin
                for (int i = 0; i < 8; i++) begin
                    logic [15:0] a_ext, b_ext;
                    a_ext = {8'b0, a_i8[i+8]};
                    b_ext = {8'b0, b_i8[i+8]};
                    r_i16[i] = a_ext * b_ext;
                end
                result = result_i16;
            end

            // i32x4 <- i16x8 extmul (low 4 words, signed)
            FD_I32X4_EXTMUL_LOW_I16X8_S: begin
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] a_ext, b_ext;
                    a_ext = $signed(a_i16[i]);
                    b_ext = $signed(b_i16[i]);
                    r_i32[i] = a_ext * b_ext;
                end
                result = result_i32;
            end

            // i32x4 <- i16x8 extmul (high 4 words, signed)
            FD_I32X4_EXTMUL_HIGH_I16X8_S: begin
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] a_ext, b_ext;
                    a_ext = $signed(a_i16[i+4]);
                    b_ext = $signed(b_i16[i+4]);
                    r_i32[i] = a_ext * b_ext;
                end
                result = result_i32;
            end

            // i32x4 <- i16x8 extmul (low 4 words, unsigned)
            FD_I32X4_EXTMUL_LOW_I16X8_U: begin
                for (int i = 0; i < 4; i++) begin
                    logic [31:0] a_ext, b_ext;
                    a_ext = {16'b0, a_i16[i]};
                    b_ext = {16'b0, b_i16[i]};
                    r_i32[i] = a_ext * b_ext;
                end
                result = result_i32;
            end

            // i32x4 <- i16x8 extmul (high 4 words, unsigned)
            FD_I32X4_EXTMUL_HIGH_I16X8_U: begin
                for (int i = 0; i < 4; i++) begin
                    logic [31:0] a_ext, b_ext;
                    a_ext = {16'b0, a_i16[i+4]};
                    b_ext = {16'b0, b_i16[i+4]};
                    r_i32[i] = a_ext * b_ext;
                end
                result = result_i32;
            end

            // i64x2 <- i32x4 extmul (low 2 dwords, signed)
            FD_I64X2_EXTMUL_LOW_I32X4_S: begin
                for (int i = 0; i < 2; i++) begin
                    logic signed [63:0] a_ext, b_ext;
                    a_ext = $signed(a_i32[i]);
                    b_ext = $signed(b_i32[i]);
                    r_i64[i] = a_ext * b_ext;
                end
                result = result_i64;
            end

            // i64x2 <- i32x4 extmul (high 2 dwords, signed)
            FD_I64X2_EXTMUL_HIGH_I32X4_S: begin
                for (int i = 0; i < 2; i++) begin
                    logic signed [63:0] a_ext, b_ext;
                    a_ext = $signed(a_i32[i+2]);
                    b_ext = $signed(b_i32[i+2]);
                    r_i64[i] = a_ext * b_ext;
                end
                result = result_i64;
            end

            // i64x2 <- i32x4 extmul (low 2 dwords, unsigned)
            FD_I64X2_EXTMUL_LOW_I32X4_U: begin
                for (int i = 0; i < 2; i++) begin
                    logic [63:0] a_ext, b_ext;
                    a_ext = {32'b0, a_i32[i]};
                    b_ext = {32'b0, b_i32[i]};
                    r_i64[i] = a_ext * b_ext;
                end
                result = result_i64;
            end

            // i64x2 <- i32x4 extmul (high 2 dwords, unsigned)
            FD_I64X2_EXTMUL_HIGH_I32X4_U: begin
                for (int i = 0; i < 2; i++) begin
                    logic [63:0] a_ext, b_ext;
                    a_ext = {32'b0, a_i32[i+2]};
                    b_ext = {32'b0, b_i32[i+2]};
                    r_i64[i] = a_ext * b_ext;
                end
                result = result_i64;
            end

            // =================================================================
            // Relaxed SIMD operations
            // =================================================================

            // i8x16.relaxed_swizzle - same as swizzle, out-of-range returns 0
            FD_I8X16_RELAXED_SWIZZLE: begin
                for (int i = 0; i < 16; i++) begin
                    logic [7:0] idx;
                    idx = b_i8[i];
                    r_i8[i] = (idx < 16) ? a_i8[idx[3:0]] : 8'b0;
                end
                result = result_i8;
            end

            // i32x4.relaxed_trunc_f32x4_s - relaxed truncation (NaN/overflow -> implementation-defined)
            FD_I32X4_RELAXED_TRUNC_F32X4_S: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = 32'h0;  // Relaxed: NaN -> 0
                    end else begin
                        real r;
                        r = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        if (r >= 2147483648.0) r_i32[i] = 32'h7FFFFFFF;
                        else if (r < -2147483648.0) r_i32[i] = 32'h80000000;
                        else r_i32[i] = $rtoi(r);
                    end
                end
                result = result_i32;
            end

            // i32x4.relaxed_trunc_f32x4_u - relaxed unsigned truncation
            FD_I32X4_RELAXED_TRUNC_F32X4_U: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = 32'h0;  // Relaxed: NaN -> 0
                    end else begin
                        real r;
                        r = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        if (r >= 4294967296.0) r_i32[i] = 32'hFFFFFFFF;
                        else if (r < 0.0) r_i32[i] = 32'h0;
                        else r_i32[i] = r;
                    end
                end
                result = result_i32;
            end

            // i32x4.relaxed_trunc_f64x2_s_zero - relaxed f64 truncation to low i32x2
            FD_I32X4_RELAXED_TRUNC_F64X2_S_ZERO: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i32[i] = 32'h0;
                    end else begin
                        real r;
                        r = $bitstoreal(a_f64[i]);
                        if (r >= 2147483648.0) r_i32[i] = 32'h7FFFFFFF;
                        else if (r < -2147483648.0) r_i32[i] = 32'h80000000;
                        else r_i32[i] = $rtoi(r);
                    end
                end
                r_i32[2] = 32'b0;
                r_i32[3] = 32'b0;
                result = result_i32;
            end

            // i32x4.relaxed_trunc_f64x2_u_zero - relaxed unsigned f64 truncation
            FD_I32X4_RELAXED_TRUNC_F64X2_U_ZERO: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i32[i] = 32'h0;
                    end else begin
                        real r;
                        r = $bitstoreal(a_f64[i]);
                        if (r >= 4294967296.0) r_i32[i] = 32'hFFFFFFFF;
                        else if (r < 0.0) r_i32[i] = 32'h0;
                        else r_i32[i] = r;
                    end
                end
                r_i32[2] = 32'b0;
                r_i32[3] = 32'b0;
                result = result_i32;
            end

            // f32x4.relaxed_madd: a*b+c (fused multiply-add)
            FD_F32X4_RELAXED_MADD: begin
                logic [31:0] c_f32 [0:3];
                for (int i = 0; i < 4; i++) begin
                    c_f32[i] = operand_c[i*32 +: 32];
                end
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i]) || f32_is_nan(c_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end else begin
                        real ra, rb, rc, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        rc = $bitstoreal(f32_to_f64_bits(c_f32[i]));
                        rr = ra * rb + rc;
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            // f32x4.relaxed_nmadd: -a*b+c (fused negative multiply-add)
            FD_F32X4_RELAXED_NMADD: begin
                logic [31:0] c_f32 [0:3];
                for (int i = 0; i < 4; i++) begin
                    c_f32[i] = operand_c[i*32 +: 32];
                end
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i]) || f32_is_nan(b_f32[i]) || f32_is_nan(c_f32[i])) begin
                        r_i32[i] = F32_CANONICAL_NAN;
                    end else begin
                        real ra, rb, rc, rr;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        rc = $bitstoreal(f32_to_f64_bits(c_f32[i]));
                        rr = -ra * rb + rc;
                        r_i32[i] = f64_to_f32_bits($realtobits(rr));
                    end
                end
                result = result_i32;
            end

            // f64x2.relaxed_madd: a*b+c
            FD_F64X2_RELAXED_MADD: begin
                logic [63:0] c_f64 [0:1];
                for (int i = 0; i < 2; i++) begin
                    c_f64[i] = operand_c[i*64 +: 64];
                end
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i]) || f64_is_nan(c_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end else begin
                        real ra, rb, rc, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        rc = $bitstoreal(c_f64[i]);
                        rr = ra * rb + rc;
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            // f64x2.relaxed_nmadd: -a*b+c
            FD_F64X2_RELAXED_NMADD: begin
                logic [63:0] c_f64 [0:1];
                for (int i = 0; i < 2; i++) begin
                    c_f64[i] = operand_c[i*64 +: 64];
                end
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i]) || f64_is_nan(b_f64[i]) || f64_is_nan(c_f64[i])) begin
                        r_i64[i] = F64_CANONICAL_NAN;
                    end else begin
                        real ra, rb, rc, rr;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        rc = $bitstoreal(c_f64[i]);
                        rr = -ra * rb + rc;
                        r_i64[i] = $realtobits(rr);
                    end
                end
                result = result_i64;
            end

            // Relaxed laneselect: bitselect using mask c (same as v128.bitselect)
            // result = (a & c) | (b & ~c)
            FD_I8X16_RELAXED_LANESELECT,
            FD_I16X8_RELAXED_LANESELECT,
            FD_I32X4_RELAXED_LANESELECT,
            FD_I64X2_RELAXED_LANESELECT: begin
                result = (operand_a & operand_c) | (operand_b & ~operand_c);
            end

            // f32x4.relaxed_min - relaxed min (any NaN ordering allowed)
            FD_F32X4_RELAXED_MIN: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = b_f32[i];  // Relaxed: return other operand
                    end else if (f32_is_nan(b_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end else begin
                        real ra, rb;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        r_i32[i] = (ra < rb) ? a_f32[i] : b_f32[i];
                    end
                end
                result = result_i32;
            end

            // f32x4.relaxed_max - relaxed max
            FD_F32X4_RELAXED_MAX: begin
                for (int i = 0; i < 4; i++) begin
                    if (f32_is_nan(a_f32[i])) begin
                        r_i32[i] = b_f32[i];
                    end else if (f32_is_nan(b_f32[i])) begin
                        r_i32[i] = a_f32[i];
                    end else begin
                        real ra, rb;
                        ra = $bitstoreal(f32_to_f64_bits(a_f32[i]));
                        rb = $bitstoreal(f32_to_f64_bits(b_f32[i]));
                        r_i32[i] = (ra > rb) ? a_f32[i] : b_f32[i];
                    end
                end
                result = result_i32;
            end

            // f64x2.relaxed_min
            FD_F64X2_RELAXED_MIN: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i64[i] = b_f64[i];
                    end else if (f64_is_nan(b_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end else begin
                        real ra, rb;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        r_i64[i] = (ra < rb) ? a_f64[i] : b_f64[i];
                    end
                end
                result = result_i64;
            end

            // f64x2.relaxed_max
            FD_F64X2_RELAXED_MAX: begin
                for (int i = 0; i < 2; i++) begin
                    if (f64_is_nan(a_f64[i])) begin
                        r_i64[i] = b_f64[i];
                    end else if (f64_is_nan(b_f64[i])) begin
                        r_i64[i] = a_f64[i];
                    end else begin
                        real ra, rb;
                        ra = $bitstoreal(a_f64[i]);
                        rb = $bitstoreal(b_f64[i]);
                        r_i64[i] = (ra > rb) ? a_f64[i] : b_f64[i];
                    end
                end
                result = result_i64;
            end

            // i16x8.relaxed_q15mulr_s - Q15 multiply with rounding (no saturation)
            FD_I16X8_RELAXED_Q15MULR_S: begin
                for (int i = 0; i < 8; i++) begin
                    logic signed [31:0] prod;
                    prod = $signed(a_i16[i]) * $signed(b_i16[i]);
                    // Round by adding 0x4000 before shifting
                    r_i16[i] = (prod + 32'sd16384) >>> 15;
                end
                result = result_i16;
            end

            // i16x8.relaxed_dot_i8x16_i7x16_s - dot product of i8x16 pairs
            // Each i16 result = sum of 2 adjacent i8*i8 products
            FD_I16X8_RELAXED_DOT_I8X16_I7X16_S: begin
                for (int i = 0; i < 8; i++) begin
                    logic signed [15:0] prod0, prod1;
                    prod0 = $signed(a_i8[i*2]) * $signed(b_i8[i*2]);
                    prod1 = $signed(a_i8[i*2+1]) * $signed(b_i8[i*2+1]);
                    r_i16[i] = prod0 + prod1;
                end
                result = result_i16;
            end

            // i32x4.relaxed_dot_i8x16_i7x16_add_s - dot product with accumulator
            // Each i32 result = sum of 4 adjacent i8*i8 products + c
            FD_I32X4_RELAXED_DOT_I8X16_I7X16_ADD_S: begin
                logic [31:0] c_i32 [0:3];
                for (int i = 0; i < 4; i++) begin
                    c_i32[i] = operand_c[i*32 +: 32];
                end
                for (int i = 0; i < 4; i++) begin
                    logic signed [31:0] prod0, prod1, prod2, prod3;
                    prod0 = $signed({{24{a_i8[i*4][7]}}, a_i8[i*4]}) * $signed({{24{b_i8[i*4][7]}}, b_i8[i*4]});
                    prod1 = $signed({{24{a_i8[i*4+1][7]}}, a_i8[i*4+1]}) * $signed({{24{b_i8[i*4+1][7]}}, b_i8[i*4+1]});
                    prod2 = $signed({{24{a_i8[i*4+2][7]}}, a_i8[i*4+2]}) * $signed({{24{b_i8[i*4+2][7]}}, b_i8[i*4+2]});
                    prod3 = $signed({{24{a_i8[i*4+3][7]}}, a_i8[i*4+3]}) * $signed({{24{b_i8[i*4+3][7]}}, b_i8[i*4+3]});
                    r_i32[i] = prod0 + prod1 + prod2 + prod3 + $signed(c_i32[i]);
                end
                result = result_i32;
            end

            // =================================================================
            // Default - pass through operand_a
            // =================================================================
            default: begin
                result = operand_a;
            end
        endcase
    end

    // Valid output follows valid input (combinational)
    assign valid_out = valid_in;

endmodule
