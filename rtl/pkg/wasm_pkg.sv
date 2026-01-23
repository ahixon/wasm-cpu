// WebAssembly CPU Package - Common Types and Definitions
// This package contains all shared types, constants, and definitions
// for the WebAssembly CPU implementation

package wasm_pkg;

    // =========================================================================
    // Value Types
    // =========================================================================
    typedef enum logic [3:0] {
        TYPE_I32     = 4'h0,  // 32-bit integer
        TYPE_I64     = 4'h1,  // 64-bit integer
        TYPE_F32     = 4'h2,  // 32-bit float (IEEE 754)
        TYPE_F64     = 4'h3,  // 64-bit float (IEEE 754)
        TYPE_V128    = 4'h4,  // 128-bit vector (SIMD)
        TYPE_FUNCREF = 4'h5,  // Function reference
        TYPE_EXTERNREF = 4'h6, // External reference
        TYPE_VOID    = 4'hF   // No type (for blocks without results)
    } valtype_t;

    // =========================================================================
    // Reference Type Constants
    // =========================================================================
    // Null reference value - used for ref.null and null checks
    // Use 0xFFFFFFFF as sentinel since valid function indices are smaller
    localparam logic [31:0] REF_NULL_VALUE = 32'hFFFF_FFFF;

    // =========================================================================
    // Instruction Opcodes (based on WebAssembly binary format)
    // =========================================================================

    // Control Instructions (0x00 - 0x11)
    typedef enum logic [7:0] {
        OP_UNREACHABLE    = 8'h00,
        OP_NOP            = 8'h01,
        OP_BLOCK          = 8'h02,
        OP_LOOP           = 8'h03,
        OP_IF             = 8'h04,
        OP_ELSE           = 8'h05,
        OP_END            = 8'h0B,
        OP_BR             = 8'h0C,
        OP_BR_IF          = 8'h0D,
        OP_BR_TABLE       = 8'h0E,
        OP_RETURN         = 8'h0F,
        OP_CALL           = 8'h10,
        OP_CALL_INDIRECT  = 8'h11,

        // Parametric Instructions (0x1A - 0x1C)
        OP_DROP           = 8'h1A,
        OP_SELECT         = 8'h1B,
        OP_SELECT_T       = 8'h1C,

        // Variable Instructions (0x20 - 0x24)
        OP_LOCAL_GET      = 8'h20,
        OP_LOCAL_SET      = 8'h21,
        OP_LOCAL_TEE      = 8'h22,
        OP_GLOBAL_GET     = 8'h23,
        OP_GLOBAL_SET     = 8'h24,

        // Table Instructions (0x25 - 0x26)
        OP_TABLE_GET      = 8'h25,
        OP_TABLE_SET      = 8'h26,

        // Memory Instructions (0x28 - 0x40)
        OP_I32_LOAD       = 8'h28,
        OP_I64_LOAD       = 8'h29,
        OP_F32_LOAD       = 8'h2A,
        OP_F64_LOAD       = 8'h2B,
        OP_I32_LOAD8_S    = 8'h2C,
        OP_I32_LOAD8_U    = 8'h2D,
        OP_I32_LOAD16_S   = 8'h2E,
        OP_I32_LOAD16_U   = 8'h2F,
        OP_I64_LOAD8_S    = 8'h30,
        OP_I64_LOAD8_U    = 8'h31,
        OP_I64_LOAD16_S   = 8'h32,
        OP_I64_LOAD16_U   = 8'h33,
        OP_I64_LOAD32_S   = 8'h34,
        OP_I64_LOAD32_U   = 8'h35,
        OP_I32_STORE      = 8'h36,
        OP_I64_STORE      = 8'h37,
        OP_F32_STORE      = 8'h38,
        OP_F64_STORE      = 8'h39,
        OP_I32_STORE8     = 8'h3A,
        OP_I32_STORE16    = 8'h3B,
        OP_I64_STORE8     = 8'h3C,
        OP_I64_STORE16    = 8'h3D,
        OP_I64_STORE32    = 8'h3E,
        OP_MEMORY_SIZE    = 8'h3F,
        OP_MEMORY_GROW    = 8'h40,

        // Numeric Constants (0x41 - 0x44)
        OP_I32_CONST      = 8'h41,
        OP_I64_CONST      = 8'h42,
        OP_F32_CONST      = 8'h43,
        OP_F64_CONST      = 8'h44,

        // i32 Comparison (0x45 - 0x4F)
        OP_I32_EQZ        = 8'h45,
        OP_I32_EQ         = 8'h46,
        OP_I32_NE         = 8'h47,
        OP_I32_LT_S       = 8'h48,
        OP_I32_LT_U       = 8'h49,
        OP_I32_GT_S       = 8'h4A,
        OP_I32_GT_U       = 8'h4B,
        OP_I32_LE_S       = 8'h4C,
        OP_I32_LE_U       = 8'h4D,
        OP_I32_GE_S       = 8'h4E,
        OP_I32_GE_U       = 8'h4F,

        // i64 Comparison (0x50 - 0x5A)
        OP_I64_EQZ        = 8'h50,
        OP_I64_EQ         = 8'h51,
        OP_I64_NE         = 8'h52,
        OP_I64_LT_S       = 8'h53,
        OP_I64_LT_U       = 8'h54,
        OP_I64_GT_S       = 8'h55,
        OP_I64_GT_U       = 8'h56,
        OP_I64_LE_S       = 8'h57,
        OP_I64_LE_U       = 8'h58,
        OP_I64_GE_S       = 8'h59,
        OP_I64_GE_U       = 8'h5A,

        // f32 Comparison (0x5B - 0x60)
        OP_F32_EQ         = 8'h5B,
        OP_F32_NE         = 8'h5C,
        OP_F32_LT         = 8'h5D,
        OP_F32_GT         = 8'h5E,
        OP_F32_LE         = 8'h5F,
        OP_F32_GE         = 8'h60,

        // f64 Comparison (0x61 - 0x66)
        OP_F64_EQ         = 8'h61,
        OP_F64_NE         = 8'h62,
        OP_F64_LT         = 8'h63,
        OP_F64_GT         = 8'h64,
        OP_F64_LE         = 8'h65,
        OP_F64_GE         = 8'h66,

        // i32 Arithmetic (0x67 - 0x78)
        OP_I32_CLZ        = 8'h67,
        OP_I32_CTZ        = 8'h68,
        OP_I32_POPCNT     = 8'h69,
        OP_I32_ADD        = 8'h6A,
        OP_I32_SUB        = 8'h6B,
        OP_I32_MUL        = 8'h6C,
        OP_I32_DIV_S      = 8'h6D,
        OP_I32_DIV_U      = 8'h6E,
        OP_I32_REM_S      = 8'h6F,
        OP_I32_REM_U      = 8'h70,
        OP_I32_AND        = 8'h71,
        OP_I32_OR         = 8'h72,
        OP_I32_XOR        = 8'h73,
        OP_I32_SHL        = 8'h74,
        OP_I32_SHR_S      = 8'h75,
        OP_I32_SHR_U      = 8'h76,
        OP_I32_ROTL       = 8'h77,
        OP_I32_ROTR       = 8'h78,

        // i64 Arithmetic (0x79 - 0x8A)
        OP_I64_CLZ        = 8'h79,
        OP_I64_CTZ        = 8'h7A,
        OP_I64_POPCNT     = 8'h7B,
        OP_I64_ADD        = 8'h7C,
        OP_I64_SUB        = 8'h7D,
        OP_I64_MUL        = 8'h7E,
        OP_I64_DIV_S      = 8'h7F,
        OP_I64_DIV_U      = 8'h80,
        OP_I64_REM_S      = 8'h81,
        OP_I64_REM_U      = 8'h82,
        OP_I64_AND        = 8'h83,
        OP_I64_OR         = 8'h84,
        OP_I64_XOR        = 8'h85,
        OP_I64_SHL        = 8'h86,
        OP_I64_SHR_S      = 8'h87,
        OP_I64_SHR_U      = 8'h88,
        OP_I64_ROTL       = 8'h89,
        OP_I64_ROTR       = 8'h8A,

        // f32 Arithmetic (0x8B - 0x98)
        OP_F32_ABS        = 8'h8B,
        OP_F32_NEG        = 8'h8C,
        OP_F32_CEIL       = 8'h8D,
        OP_F32_FLOOR      = 8'h8E,
        OP_F32_TRUNC      = 8'h8F,
        OP_F32_NEAREST    = 8'h90,
        OP_F32_SQRT       = 8'h91,
        OP_F32_ADD        = 8'h92,
        OP_F32_SUB        = 8'h93,
        OP_F32_MUL        = 8'h94,
        OP_F32_DIV        = 8'h95,
        OP_F32_MIN        = 8'h96,
        OP_F32_MAX        = 8'h97,
        OP_F32_COPYSIGN   = 8'h98,

        // f64 Arithmetic (0x99 - 0xA6)
        OP_F64_ABS        = 8'h99,
        OP_F64_NEG        = 8'h9A,
        OP_F64_CEIL       = 8'h9B,
        OP_F64_FLOOR      = 8'h9C,
        OP_F64_TRUNC      = 8'h9D,
        OP_F64_NEAREST    = 8'h9E,
        OP_F64_SQRT       = 8'h9F,
        OP_F64_ADD        = 8'hA0,
        OP_F64_SUB        = 8'hA1,
        OP_F64_MUL        = 8'hA2,
        OP_F64_DIV        = 8'hA3,
        OP_F64_MIN        = 8'hA4,
        OP_F64_MAX        = 8'hA5,
        OP_F64_COPYSIGN   = 8'hA6,

        // Conversions (0xA7 - 0xBF)
        OP_I32_WRAP_I64       = 8'hA7,
        OP_I32_TRUNC_F32_S    = 8'hA8,
        OP_I32_TRUNC_F32_U    = 8'hA9,
        OP_I32_TRUNC_F64_S    = 8'hAA,
        OP_I32_TRUNC_F64_U    = 8'hAB,
        OP_I64_EXTEND_I32_S   = 8'hAC,
        OP_I64_EXTEND_I32_U   = 8'hAD,
        OP_I64_TRUNC_F32_S    = 8'hAE,
        OP_I64_TRUNC_F32_U    = 8'hAF,
        OP_I64_TRUNC_F64_S    = 8'hB0,
        OP_I64_TRUNC_F64_U    = 8'hB1,
        OP_F32_CONVERT_I32_S  = 8'hB2,
        OP_F32_CONVERT_I32_U  = 8'hB3,
        OP_F32_CONVERT_I64_S  = 8'hB4,
        OP_F32_CONVERT_I64_U  = 8'hB5,
        OP_F32_DEMOTE_F64     = 8'hB6,
        OP_F64_CONVERT_I32_S  = 8'hB7,
        OP_F64_CONVERT_I32_U  = 8'hB8,
        OP_F64_CONVERT_I64_S  = 8'hB9,
        OP_F64_CONVERT_I64_U  = 8'hBA,
        OP_F64_PROMOTE_F32    = 8'hBB,
        OP_I32_REINTERPRET_F32 = 8'hBC,
        OP_I64_REINTERPRET_F64 = 8'hBD,
        OP_F32_REINTERPRET_I32 = 8'hBE,
        OP_F64_REINTERPRET_I64 = 8'hBF,

        // Sign extension (0xC0 - 0xC4)
        OP_I32_EXTEND8_S  = 8'hC0,
        OP_I32_EXTEND16_S = 8'hC1,
        OP_I64_EXTEND8_S  = 8'hC2,
        OP_I64_EXTEND16_S = 8'hC3,
        OP_I64_EXTEND32_S = 8'hC4,

        // Reference types (0xD0 - 0xD6)
        OP_REF_NULL       = 8'hD0,  // ref.null t -> (ref null t)
        OP_REF_IS_NULL    = 8'hD1,  // (ref t) -> i32
        OP_REF_FUNC       = 8'hD2,  // $funcidx -> funcref
        OP_REF_AS_NON_NULL = 8'hD3, // (ref null t) -> (ref t) or trap
        OP_BR_ON_NULL     = 8'hD5,  // branch if reference is null
        OP_BR_ON_NON_NULL = 8'hD6,  // branch if reference is not null

        // Prefix for extended opcodes
        OP_PREFIX_FC      = 8'hFC,
        OP_PREFIX_FD      = 8'hFD
    } opcode_t;

    // =========================================================================
    // Extended Opcodes (0xFC prefix)
    // =========================================================================
    // These are sub-opcodes following the 0xFC prefix byte
    typedef enum logic [7:0] {
        // Saturating truncation instructions
        FC_I32_TRUNC_SAT_F32_S = 8'h00,
        FC_I32_TRUNC_SAT_F32_U = 8'h01,
        FC_I32_TRUNC_SAT_F64_S = 8'h02,
        FC_I32_TRUNC_SAT_F64_U = 8'h03,
        FC_I64_TRUNC_SAT_F32_S = 8'h04,
        FC_I64_TRUNC_SAT_F32_U = 8'h05,
        FC_I64_TRUNC_SAT_F64_S = 8'h06,
        FC_I64_TRUNC_SAT_F64_U = 8'h07,

        // Bulk memory operations
        FC_MEMORY_INIT        = 8'h08,  // memory.init data_idx mem_idx
        FC_DATA_DROP          = 8'h09,  // data.drop data_idx
        FC_MEMORY_COPY        = 8'h0A,  // memory.copy dst_mem src_mem
        FC_MEMORY_FILL        = 8'h0B,  // memory.fill mem_idx

        // Table operations
        FC_TABLE_INIT         = 8'h0C,  // table.init elem_idx table_idx
        FC_ELEM_DROP          = 8'h0D,  // elem.drop elem_idx
        FC_TABLE_COPY         = 8'h0E,  // table.copy dst_table src_table
        FC_TABLE_GROW         = 8'h0F,  // table.grow table_idx
        FC_TABLE_SIZE         = 8'h10,  // table.size table_idx
        FC_TABLE_FILL         = 8'h11   // table.fill table_idx
    } fc_opcode_t;

    // =========================================================================
    // SIMD Opcodes (0xFD prefix) - WebAssembly SIMD v128 operations
    // =========================================================================
    // These are sub-opcodes following the 0xFD prefix byte (LEB128 encoded)
    typedef enum logic [8:0] {
        // Memory operations (0x00-0x0B)
        FD_V128_LOAD              = 9'h000,  // v128.load memarg
        FD_V128_LOAD8X8_S         = 9'h001,  // v128.load8x8_s memarg
        FD_V128_LOAD8X8_U         = 9'h002,  // v128.load8x8_u memarg
        FD_V128_LOAD16X4_S        = 9'h003,  // v128.load16x4_s memarg
        FD_V128_LOAD16X4_U        = 9'h004,  // v128.load16x4_u memarg
        FD_V128_LOAD32X2_S        = 9'h005,  // v128.load32x2_s memarg
        FD_V128_LOAD32X2_U        = 9'h006,  // v128.load32x2_u memarg
        FD_V128_LOAD8_SPLAT       = 9'h007,  // v128.load8_splat memarg
        FD_V128_LOAD16_SPLAT      = 9'h008,  // v128.load16_splat memarg
        FD_V128_LOAD32_SPLAT      = 9'h009,  // v128.load32_splat memarg
        FD_V128_LOAD64_SPLAT      = 9'h00A,  // v128.load64_splat memarg
        FD_V128_STORE             = 9'h00B,  // v128.store memarg

        // Constant (0x0C)
        FD_V128_CONST             = 9'h00C,  // v128.const bytes[16]

        // Shuffle/swizzle (0x0D-0x0E)
        FD_I8X16_SHUFFLE          = 9'h00D,  // i8x16.shuffle lane[16]
        FD_I8X16_SWIZZLE          = 9'h00E,  // i8x16.swizzle

        // Splat operations (0x0F-0x14)
        FD_I8X16_SPLAT            = 9'h00F,  // i8x16.splat
        FD_I16X8_SPLAT            = 9'h010,  // i16x8.splat
        FD_I32X4_SPLAT            = 9'h011,  // i32x4.splat
        FD_I64X2_SPLAT            = 9'h012,  // i64x2.splat
        FD_F32X4_SPLAT            = 9'h013,  // f32x4.splat
        FD_F64X2_SPLAT            = 9'h014,  // f64x2.splat

        // Lane extract/replace - i8x16 (0x15-0x18)
        FD_I8X16_EXTRACT_LANE_S   = 9'h015,  // i8x16.extract_lane_s laneidx
        FD_I8X16_EXTRACT_LANE_U   = 9'h016,  // i8x16.extract_lane_u laneidx
        FD_I8X16_REPLACE_LANE     = 9'h017,  // i8x16.replace_lane laneidx

        // Lane extract/replace - i16x8 (0x18-0x1B)
        FD_I16X8_EXTRACT_LANE_S   = 9'h018,  // i16x8.extract_lane_s laneidx
        FD_I16X8_EXTRACT_LANE_U   = 9'h019,  // i16x8.extract_lane_u laneidx
        FD_I16X8_REPLACE_LANE     = 9'h01A,  // i16x8.replace_lane laneidx

        // Lane extract/replace - i32x4 (0x1B-0x1C)
        FD_I32X4_EXTRACT_LANE     = 9'h01B,  // i32x4.extract_lane laneidx
        FD_I32X4_REPLACE_LANE     = 9'h01C,  // i32x4.replace_lane laneidx

        // Lane extract/replace - i64x2 (0x1D-0x1E)
        FD_I64X2_EXTRACT_LANE     = 9'h01D,  // i64x2.extract_lane laneidx
        FD_I64X2_REPLACE_LANE     = 9'h01E,  // i64x2.replace_lane laneidx

        // Lane extract/replace - f32x4 (0x1F-0x20)
        FD_F32X4_EXTRACT_LANE     = 9'h01F,  // f32x4.extract_lane laneidx
        FD_F32X4_REPLACE_LANE     = 9'h020,  // f32x4.replace_lane laneidx

        // Lane extract/replace - f64x2 (0x21-0x22)
        FD_F64X2_EXTRACT_LANE     = 9'h021,  // f64x2.extract_lane laneidx
        FD_F64X2_REPLACE_LANE     = 9'h022,  // f64x2.replace_lane laneidx

        // i8x16 comparisons (0x23-0x2E)
        FD_I8X16_EQ               = 9'h023,
        FD_I8X16_NE               = 9'h024,
        FD_I8X16_LT_S             = 9'h025,
        FD_I8X16_LT_U             = 9'h026,
        FD_I8X16_GT_S             = 9'h027,
        FD_I8X16_GT_U             = 9'h028,
        FD_I8X16_LE_S             = 9'h029,
        FD_I8X16_LE_U             = 9'h02A,
        FD_I8X16_GE_S             = 9'h02B,
        FD_I8X16_GE_U             = 9'h02C,

        // i16x8 comparisons (0x2D-0x38)
        FD_I16X8_EQ               = 9'h02D,
        FD_I16X8_NE               = 9'h02E,
        FD_I16X8_LT_S             = 9'h02F,
        FD_I16X8_LT_U             = 9'h030,
        FD_I16X8_GT_S             = 9'h031,
        FD_I16X8_GT_U             = 9'h032,
        FD_I16X8_LE_S             = 9'h033,
        FD_I16X8_LE_U             = 9'h034,
        FD_I16X8_GE_S             = 9'h035,
        FD_I16X8_GE_U             = 9'h036,

        // i32x4 comparisons (0x37-0x42)
        FD_I32X4_EQ               = 9'h037,
        FD_I32X4_NE               = 9'h038,
        FD_I32X4_LT_S             = 9'h039,
        FD_I32X4_LT_U             = 9'h03A,
        FD_I32X4_GT_S             = 9'h03B,
        FD_I32X4_GT_U             = 9'h03C,
        FD_I32X4_LE_S             = 9'h03D,
        FD_I32X4_LE_U             = 9'h03E,
        FD_I32X4_GE_S             = 9'h03F,
        FD_I32X4_GE_U             = 9'h040,

        // f32x4 comparisons (0x41-0x46)
        FD_F32X4_EQ               = 9'h041,
        FD_F32X4_NE               = 9'h042,
        FD_F32X4_LT               = 9'h043,
        FD_F32X4_GT               = 9'h044,
        FD_F32X4_LE               = 9'h045,
        FD_F32X4_GE               = 9'h046,

        // f64x2 comparisons (0x47-0x4C)
        FD_F64X2_EQ               = 9'h047,
        FD_F64X2_NE               = 9'h048,
        FD_F64X2_LT               = 9'h049,
        FD_F64X2_GT               = 9'h04A,
        FD_F64X2_LE               = 9'h04B,
        FD_F64X2_GE               = 9'h04C,

        // v128 bitwise (0x4D-0x51)
        FD_V128_NOT               = 9'h04D,
        FD_V128_AND               = 9'h04E,
        FD_V128_ANDNOT            = 9'h04F,
        FD_V128_OR                = 9'h050,
        FD_V128_XOR               = 9'h051,
        FD_V128_BITSELECT         = 9'h052,
        FD_V128_ANY_TRUE          = 9'h053,

        // Load lane operations (0x54-0x5D)
        FD_V128_LOAD8_LANE        = 9'h054,
        FD_V128_LOAD16_LANE       = 9'h055,
        FD_V128_LOAD32_LANE       = 9'h056,
        FD_V128_LOAD64_LANE       = 9'h057,
        FD_V128_STORE8_LANE       = 9'h058,
        FD_V128_STORE16_LANE      = 9'h059,
        FD_V128_STORE32_LANE      = 9'h05A,
        FD_V128_STORE64_LANE      = 9'h05B,
        FD_V128_LOAD32_ZERO       = 9'h05C,
        FD_V128_LOAD64_ZERO       = 9'h05D,

        // f32x4 arithmetic (0x5E-0x6B)
        FD_F32X4_DEMOTE_F64X2_ZERO = 9'h05E,
        FD_F64X2_PROMOTE_LOW_F32X4 = 9'h05F,

        // i8x16 arithmetic (0x60-0x71)
        FD_I8X16_ABS              = 9'h060,
        FD_I8X16_NEG              = 9'h061,
        FD_I8X16_POPCNT           = 9'h062,
        FD_I8X16_ALL_TRUE         = 9'h063,
        FD_I8X16_BITMASK          = 9'h064,
        FD_I8X16_NARROW_I16X8_S   = 9'h065,
        FD_I8X16_NARROW_I16X8_U   = 9'h066,
        FD_F32X4_CEIL             = 9'h067,
        FD_F32X4_FLOOR            = 9'h068,
        FD_F32X4_TRUNC            = 9'h069,
        FD_F32X4_NEAREST          = 9'h06A,
        FD_I8X16_SHL              = 9'h06B,
        FD_I8X16_SHR_S            = 9'h06C,
        FD_I8X16_SHR_U            = 9'h06D,
        FD_I8X16_ADD              = 9'h06E,
        FD_I8X16_ADD_SAT_S        = 9'h06F,
        FD_I8X16_ADD_SAT_U        = 9'h070,
        FD_I8X16_SUB              = 9'h071,
        FD_I8X16_SUB_SAT_S        = 9'h072,
        FD_I8X16_SUB_SAT_U        = 9'h073,
        FD_F64X2_CEIL             = 9'h074,
        FD_F64X2_FLOOR            = 9'h075,
        FD_I8X16_MIN_S            = 9'h076,
        FD_I8X16_MIN_U            = 9'h077,
        FD_I8X16_MAX_S            = 9'h078,
        FD_I8X16_MAX_U            = 9'h079,
        FD_F64X2_TRUNC            = 9'h07A,
        FD_I8X16_AVGR_U           = 9'h07B,

        // Extended pairwise addition (0x7C-0x7F)
        FD_I16X8_EXTADD_PAIRWISE_I8X16_S = 9'h07C,
        FD_I16X8_EXTADD_PAIRWISE_I8X16_U = 9'h07D,
        FD_I32X4_EXTADD_PAIRWISE_I16X8_S = 9'h07E,
        FD_I32X4_EXTADD_PAIRWISE_I16X8_U = 9'h07F,

        // i16x8 arithmetic (0x80-0x9B)
        FD_I16X8_ABS              = 9'h080,
        FD_I16X8_NEG              = 9'h081,
        FD_I16X8_Q15MULR_SAT_S    = 9'h082,
        FD_I16X8_ALL_TRUE         = 9'h083,
        FD_I16X8_BITMASK          = 9'h084,
        FD_I16X8_NARROW_I32X4_S   = 9'h085,
        FD_I16X8_NARROW_I32X4_U   = 9'h086,
        FD_I16X8_EXTEND_LOW_I8X16_S  = 9'h087,
        FD_I16X8_EXTEND_HIGH_I8X16_S = 9'h088,
        FD_I16X8_EXTEND_LOW_I8X16_U  = 9'h089,
        FD_I16X8_EXTEND_HIGH_I8X16_U = 9'h08A,
        FD_I16X8_SHL              = 9'h08B,
        FD_I16X8_SHR_S            = 9'h08C,
        FD_I16X8_SHR_U            = 9'h08D,
        FD_I16X8_ADD              = 9'h08E,
        FD_I16X8_ADD_SAT_S        = 9'h08F,
        FD_I16X8_ADD_SAT_U        = 9'h090,
        FD_I16X8_SUB              = 9'h091,
        FD_I16X8_SUB_SAT_S        = 9'h092,
        FD_I16X8_SUB_SAT_U        = 9'h093,
        FD_F64X2_NEAREST          = 9'h094,
        FD_I16X8_MUL              = 9'h095,
        FD_I16X8_MIN_S            = 9'h096,
        FD_I16X8_MIN_U            = 9'h097,
        FD_I16X8_MAX_S            = 9'h098,
        FD_I16X8_MAX_U            = 9'h099,
        // 0x9A unused
        FD_I16X8_AVGR_U           = 9'h09B,

        // Extended multiply (0x9C-0x9F)
        FD_I16X8_EXTMUL_LOW_I8X16_S  = 9'h09C,
        FD_I16X8_EXTMUL_HIGH_I8X16_S = 9'h09D,
        FD_I16X8_EXTMUL_LOW_I8X16_U  = 9'h09E,
        FD_I16X8_EXTMUL_HIGH_I8X16_U = 9'h09F,

        // i32x4 arithmetic (0xA0-0xBF)
        FD_I32X4_ABS              = 9'h0A0,
        FD_I32X4_NEG              = 9'h0A1,
        // 0xA2 unused
        FD_I32X4_ALL_TRUE         = 9'h0A3,
        FD_I32X4_BITMASK          = 9'h0A4,
        // 0xA5-0xA6 unused
        FD_I32X4_EXTEND_LOW_I16X8_S  = 9'h0A7,
        FD_I32X4_EXTEND_HIGH_I16X8_S = 9'h0A8,
        FD_I32X4_EXTEND_LOW_I16X8_U  = 9'h0A9,
        FD_I32X4_EXTEND_HIGH_I16X8_U = 9'h0AA,
        FD_I32X4_SHL              = 9'h0AB,
        FD_I32X4_SHR_S            = 9'h0AC,
        FD_I32X4_SHR_U            = 9'h0AD,
        FD_I32X4_ADD              = 9'h0AE,
        // 0xAF-0xB0 unused
        FD_I32X4_SUB              = 9'h0B1,
        // 0xB2-0xB4 unused
        FD_I32X4_MUL              = 9'h0B5,
        FD_I32X4_MIN_S            = 9'h0B6,
        FD_I32X4_MIN_U            = 9'h0B7,
        FD_I32X4_MAX_S            = 9'h0B8,
        FD_I32X4_MAX_U            = 9'h0B9,
        FD_I32X4_DOT_I16X8_S      = 9'h0BA,
        // 0xBB unused
        FD_I32X4_EXTMUL_LOW_I16X8_S  = 9'h0BC,
        FD_I32X4_EXTMUL_HIGH_I16X8_S = 9'h0BD,
        FD_I32X4_EXTMUL_LOW_I16X8_U  = 9'h0BE,
        FD_I32X4_EXTMUL_HIGH_I16X8_U = 9'h0BF,

        // i64x2 arithmetic (0xC0-0xDF)
        FD_I64X2_ABS              = 9'h0C0,
        FD_I64X2_NEG              = 9'h0C1,
        // 0xC2 unused
        FD_I64X2_ALL_TRUE         = 9'h0C3,
        FD_I64X2_BITMASK          = 9'h0C4,
        // 0xC5-0xC6 unused
        FD_I64X2_EXTEND_LOW_I32X4_S  = 9'h0C7,
        FD_I64X2_EXTEND_HIGH_I32X4_S = 9'h0C8,
        FD_I64X2_EXTEND_LOW_I32X4_U  = 9'h0C9,
        FD_I64X2_EXTEND_HIGH_I32X4_U = 9'h0CA,
        FD_I64X2_SHL              = 9'h0CB,
        FD_I64X2_SHR_S            = 9'h0CC,
        FD_I64X2_SHR_U            = 9'h0CD,
        FD_I64X2_ADD              = 9'h0CE,
        // 0xCF-0xD0 unused
        FD_I64X2_SUB              = 9'h0D1,
        // 0xD2-0xD4 unused
        FD_I64X2_MUL              = 9'h0D5,
        FD_I64X2_EQ               = 9'h0D6,
        FD_I64X2_NE               = 9'h0D7,
        FD_I64X2_LT_S             = 9'h0D8,
        FD_I64X2_GT_S             = 9'h0D9,
        FD_I64X2_LE_S             = 9'h0DA,
        FD_I64X2_GE_S             = 9'h0DB,
        FD_I64X2_EXTMUL_LOW_I32X4_S  = 9'h0DC,
        FD_I64X2_EXTMUL_HIGH_I32X4_S = 9'h0DD,
        FD_I64X2_EXTMUL_LOW_I32X4_U  = 9'h0DE,
        FD_I64X2_EXTMUL_HIGH_I32X4_U = 9'h0DF,

        // f32x4 arithmetic (0xE0-0xF3)
        FD_F32X4_ABS              = 9'h0E0,
        FD_F32X4_NEG              = 9'h0E1,
        // 0xE2 unused
        FD_F32X4_SQRT             = 9'h0E3,
        FD_F32X4_ADD              = 9'h0E4,
        FD_F32X4_SUB              = 9'h0E5,
        FD_F32X4_MUL              = 9'h0E6,
        FD_F32X4_DIV              = 9'h0E7,
        FD_F32X4_MIN              = 9'h0E8,
        FD_F32X4_MAX              = 9'h0E9,
        FD_F32X4_PMIN             = 9'h0EA,
        FD_F32X4_PMAX             = 9'h0EB,

        // f64x2 arithmetic (0xEC-0xFF)
        FD_F64X2_ABS              = 9'h0EC,
        FD_F64X2_NEG              = 9'h0ED,
        // 0xEE unused
        FD_F64X2_SQRT             = 9'h0EF,
        FD_F64X2_ADD              = 9'h0F0,
        FD_F64X2_SUB              = 9'h0F1,
        FD_F64X2_MUL              = 9'h0F2,
        FD_F64X2_DIV              = 9'h0F3,
        FD_F64X2_MIN              = 9'h0F4,
        FD_F64X2_MAX              = 9'h0F5,
        FD_F64X2_PMIN             = 9'h0F6,
        FD_F64X2_PMAX             = 9'h0F7,

        // Conversions (0xF8-0xFF and 0x100+)
        FD_I32X4_TRUNC_SAT_F32X4_S = 9'h0F8,
        FD_I32X4_TRUNC_SAT_F32X4_U = 9'h0F9,
        FD_F32X4_CONVERT_I32X4_S   = 9'h0FA,
        FD_F32X4_CONVERT_I32X4_U   = 9'h0FB,
        FD_I32X4_TRUNC_SAT_F64X2_S_ZERO = 9'h0FC,
        FD_I32X4_TRUNC_SAT_F64X2_U_ZERO = 9'h0FD,
        FD_F64X2_CONVERT_LOW_I32X4_S = 9'h0FE,
        FD_F64X2_CONVERT_LOW_I32X4_U = 9'h0FF,

        // Relaxed SIMD (0x100+)
        FD_I8X16_RELAXED_SWIZZLE  = 9'h100,
        FD_I32X4_RELAXED_TRUNC_F32X4_S = 9'h101,
        FD_I32X4_RELAXED_TRUNC_F32X4_U = 9'h102,
        FD_I32X4_RELAXED_TRUNC_F64X2_S_ZERO = 9'h103,
        FD_I32X4_RELAXED_TRUNC_F64X2_U_ZERO = 9'h104,
        FD_F32X4_RELAXED_MADD = 9'h105,
        FD_F32X4_RELAXED_NMADD = 9'h106,
        FD_F64X2_RELAXED_MADD = 9'h107,
        FD_F64X2_RELAXED_NMADD = 9'h108,
        FD_I8X16_RELAXED_LANESELECT = 9'h109,
        FD_I16X8_RELAXED_LANESELECT = 9'h10A,
        FD_I32X4_RELAXED_LANESELECT = 9'h10B,
        FD_I64X2_RELAXED_LANESELECT = 9'h10C,
        FD_F32X4_RELAXED_MIN = 9'h10D,
        FD_F32X4_RELAXED_MAX = 9'h10E,
        FD_F64X2_RELAXED_MIN = 9'h10F,
        FD_F64X2_RELAXED_MAX = 9'h110,
        FD_I16X8_RELAXED_Q15MULR_S = 9'h111,
        FD_I16X8_RELAXED_DOT_I8X16_I7X16_S = 9'h112,
        FD_I32X4_RELAXED_DOT_I8X16_I7X16_ADD_S = 9'h113
    } fd_opcode_t;

    // =========================================================================
    // ALU Operation Types
    // =========================================================================
    typedef enum logic [4:0] {
        ALU_ADD,
        ALU_SUB,
        ALU_MUL,
        ALU_DIV_S,
        ALU_DIV_U,
        ALU_REM_S,
        ALU_REM_U,
        ALU_AND,
        ALU_OR,
        ALU_XOR,
        ALU_SHL,
        ALU_SHR_S,
        ALU_SHR_U,
        ALU_ROTL,
        ALU_ROTR,
        ALU_CLZ,
        ALU_CTZ,
        ALU_POPCNT,
        ALU_EQZ,
        ALU_EQ,
        ALU_NE,
        ALU_LT_S,
        ALU_LT_U,
        ALU_GT_S,
        ALU_GT_U,
        ALU_LE_S,
        ALU_LE_U,
        ALU_GE_S,
        ALU_GE_U
    } alu_op_t;

    // =========================================================================
    // FPU Operation Types
    // =========================================================================
    typedef enum logic [4:0] {
        FPU_ADD,
        FPU_SUB,
        FPU_MUL,
        FPU_DIV,
        FPU_MIN,
        FPU_MAX,
        FPU_ABS,
        FPU_NEG,
        FPU_CEIL,
        FPU_FLOOR,
        FPU_TRUNC,
        FPU_NEAREST,
        FPU_SQRT,
        FPU_COPYSIGN,
        FPU_EQ,
        FPU_NE,
        FPU_LT,
        FPU_GT,
        FPU_LE,
        FPU_GE
    } fpu_op_t;

    // =========================================================================
    // Memory Operation Types (WASM-specific, includes sign extension info)
    // =========================================================================
    typedef enum logic [4:0] {
        MEM_LOAD_I32,
        MEM_LOAD_I64,
        MEM_LOAD_F32,
        MEM_LOAD_F64,
        MEM_LOAD_I8_S,
        MEM_LOAD_I8_U,
        MEM_LOAD_I16_S,
        MEM_LOAD_I16_U,
        MEM_LOAD_I32_S,
        MEM_LOAD_I32_U,
        MEM_STORE_I32,
        MEM_STORE_I64,
        MEM_STORE_I8,
        MEM_STORE_I16,
        MEM_STORE_I32_FROM_I64,
        // SIMD memory operations (v128 = 16 bytes)
        MEM_LOAD_V128,
        MEM_STORE_V128,
        // SIMD lane load/store operations
        MEM_LOAD_V128_8_SPLAT,
        MEM_LOAD_V128_16_SPLAT,
        MEM_LOAD_V128_32_SPLAT,
        MEM_LOAD_V128_64_SPLAT,
        MEM_LOAD_V128_8X8_S,
        MEM_LOAD_V128_8X8_U,
        MEM_LOAD_V128_16X4_S,
        MEM_LOAD_V128_16X4_U,
        MEM_LOAD_V128_32X2_S,
        MEM_LOAD_V128_32X2_U,
        MEM_LOAD_V128_32_ZERO,
        MEM_LOAD_V128_64_ZERO
    } mem_op_t;

    // =========================================================================
    // Memory Bus Interface (clean interface for external memory/AXI)
    // =========================================================================

    // Memory access size (power of 2 bytes)
    typedef enum logic [2:0] {
        MEM_SIZE_1  = 3'b000,  // 1 byte
        MEM_SIZE_2  = 3'b001,  // 2 bytes
        MEM_SIZE_4  = 3'b010,  // 4 bytes
        MEM_SIZE_8  = 3'b011,  // 8 bytes
        MEM_SIZE_16 = 3'b100   // 16 bytes (v128)
    } mem_size_t;

    // Memory bus request (master -> slave)
    // Simple valid/ready handshake, compatible with AXI-lite conversion
    typedef struct packed {
        logic         valid;      // Request valid
        logic         write;      // 0 = read, 1 = write
        logic [31:0]  addr;       // Byte address
        mem_size_t    size;       // Access size (1/2/4/8/16 bytes)
        logic [127:0] wdata;      // Write data (little-endian, right-aligned)
    } mem_bus_req_t;

    // Memory bus response (slave -> master)
    typedef struct packed {
        logic         ready;      // Can accept request this cycle
        logic         rvalid;     // Read response valid
        logic [127:0] rdata;      // Read data (little-endian, zero-extended)
        logic         error;      // Access error (out of bounds, etc.)
    } mem_bus_resp_t;

    // Memory management request (WASM-specific, separate from data path)
    typedef struct packed {
        logic        init_valid;       // Pulse to initialize memory
        logic [31:0] init_pages;       // Initial page count
        logic [31:0] init_max_pages;   // Maximum pages (0 = use default)
        logic        grow_valid;       // Request to grow memory
        logic [31:0] grow_pages;       // Number of pages to add
    } mem_mgmt_req_t;

    // Memory management response
    typedef struct packed {
        logic [31:0] current_pages;    // Current page count
        logic [31:0] grow_result;      // Previous size or -1 on failure
        logic        grow_done;        // Grow operation complete
    } mem_mgmt_resp_t;

    // =========================================================================
    // Table Bus Interface (for externalized table storage)
    // =========================================================================

    // Table bus request (CPU -> Table)
    typedef struct packed {
        logic        valid;
        logic        write;       // 0=read, 1=write
        logic [1:0]  table_idx;   // Which table (0-3)
        logic [15:0] elem_idx;    // Element index
        logic [31:0] wdata;       // Write data
    } table_bus_req_t;

    // Table bus response (Table -> CPU) - single-cycle combinational read
    typedef struct packed {
        logic        ready;
        logic        rvalid;
        logic [31:0] rdata;
        logic [3:0]  elem_type;   // TYPE_FUNCREF or TYPE_EXTERNREF
        logic        error;       // Out of bounds
    } table_bus_resp_t;

    // Table management request
    typedef struct packed {
        logic        init_valid;
        logic [1:0]  init_table_idx;
        logic [15:0] init_size;
        logic [15:0] init_max_size;
        logic [3:0]  init_type;
        logic        elem_init_valid;
        logic [1:0]  elem_table_idx;
        logic [15:0] elem_idx;
        logic [31:0] elem_value;
        logic        grow_valid;
        logic [1:0]  grow_table_idx;
        logic [31:0] grow_delta;
        logic [31:0] grow_init_val;
    } table_mgmt_req_t;

    // Table management response
    // Note: Arrays flattened to avoid unpacked arrays in packed struct
    typedef struct packed {
        logic [15:0] size_0;
        logic [15:0] size_1;
        logic [15:0] size_2;
        logic [15:0] size_3;
        logic [15:0] max_size_0;
        logic [15:0] max_size_1;
        logic [15:0] max_size_2;
        logic [15:0] max_size_3;
        logic [3:0]  elem_type_0;
        logic [3:0]  elem_type_1;
        logic [3:0]  elem_type_2;
        logic [3:0]  elem_type_3;
        logic [31:0] grow_result;
        logic        grow_done;
    } table_mgmt_resp_t;

    // Helper function: Convert mem_op_t to mem_size_t
    function automatic mem_size_t mem_op_to_size(mem_op_t op);
        case (op)
            MEM_LOAD_I8_S, MEM_LOAD_I8_U, MEM_STORE_I8,
            MEM_LOAD_V128_8_SPLAT:
                return MEM_SIZE_1;
            MEM_LOAD_I16_S, MEM_LOAD_I16_U, MEM_STORE_I16,
            MEM_LOAD_V128_16_SPLAT:
                return MEM_SIZE_2;
            MEM_LOAD_I32, MEM_LOAD_F32, MEM_LOAD_I32_S, MEM_LOAD_I32_U,
            MEM_STORE_I32, MEM_STORE_I32_FROM_I64,
            MEM_LOAD_V128_32_SPLAT, MEM_LOAD_V128_32_ZERO:
                return MEM_SIZE_4;
            MEM_LOAD_I64, MEM_LOAD_F64, MEM_STORE_I64,
            MEM_LOAD_V128_64_SPLAT, MEM_LOAD_V128_64_ZERO,
            MEM_LOAD_V128_8X8_S, MEM_LOAD_V128_8X8_U,
            MEM_LOAD_V128_16X4_S, MEM_LOAD_V128_16X4_U,
            MEM_LOAD_V128_32X2_S, MEM_LOAD_V128_32X2_U:
                return MEM_SIZE_8;
            MEM_LOAD_V128, MEM_STORE_V128:
                return MEM_SIZE_16;
            default:
                return MEM_SIZE_4;
        endcase
    endfunction

    // Helper function: Check if mem_op_t is a write operation
    function automatic logic mem_op_is_write(mem_op_t op);
        case (op)
            MEM_STORE_I32, MEM_STORE_I64, MEM_STORE_I8,
            MEM_STORE_I16, MEM_STORE_I32_FROM_I64,
            MEM_STORE_V128:
                return 1'b1;
            default:
                return 1'b0;
        endcase
    endfunction

    // Helper function: Check if mem_op_t requires sign extension
    function automatic logic mem_op_is_signed(mem_op_t op);
        case (op)
            MEM_LOAD_I8_S, MEM_LOAD_I16_S, MEM_LOAD_I32_S:
                return 1'b1;
            default:
                return 1'b0;
        endcase
    endfunction

    // =========================================================================
    // Execution State
    // =========================================================================
    typedef enum logic [4:0] {
        STATE_IDLE,
        STATE_FETCH,
        STATE_DECODE,
        STATE_EXECUTE,
        STATE_MEMORY,
        STATE_WRITEBACK,
        STATE_BRANCH,
        STATE_CALL,
        STATE_RETURN,
        STATE_SCAN_ELSE,     // Scanning for else/end in if-else
        STATE_SCAN_END,      // Scanning for end (skipping block)
        STATE_SCAN_BR_TABLE, // Scanning br_table during end scan
        STATE_BR_TABLE,      // Processing br_table targets
        STATE_BR_UNWIND,     // Unwinding stack after branch
        STATE_CAPTURE_RESULTS, // Capturing multi-value results before halt
        STATE_TABLE_GROW_WAIT, // Waiting for table.grow size update to propagate
        STATE_TABLE_CACHE_MISS, // Waiting for table entry fetch from memory
        STATE_FILL,             // Fill loop for table.grow/table.fill/memory.fill
        STATE_TABLE_INIT,       // table.init copy loop (read elem segment, write table)
        STATE_TABLE_COPY,       // table.copy copy loop (read table, write table)
        STATE_MEMORY_COPY,      // memory.copy/memory.init byte-level copy loop
        STATE_TRAP,
        STATE_HALT,
        STATE_EXT_HALT       // Halted by external supervisor, waiting for resume
    } exec_state_t;

    // =========================================================================
    // Trap Types
    // =========================================================================
    typedef enum logic [4:0] {
        TRAP_NONE,
        TRAP_UNREACHABLE,
        TRAP_INT_DIV_ZERO,
        TRAP_INT_OVERFLOW,
        TRAP_INVALID_CONV,
        TRAP_OUT_OF_BOUNDS,
        TRAP_INDIRECT_CALL_TYPE_MISMATCH,
        TRAP_UNDEFINED_ELEMENT,
        TRAP_UNINITIALIZED_ELEMENT,
        TRAP_STACK_OVERFLOW,
        TRAP_STACK_UNDERFLOW,
        TRAP_CALL_STACK_EXHAUSTED,
        TRAP_IMPORT,         // Unresolved import (WASI call) - requires S-mode handling
        TRAP_MEMORY_GROW,    // memory.grow request - requires S-mode approval
        TRAP_NULL_REFERENCE, // Null reference dereference (ref.as_non_null)
        TRAP_TABLE_GROW      // table.grow request - requires S-mode approval
    } trap_t;

    // =========================================================================
    // Configuration Parameters
    // =========================================================================
    parameter int STACK_DEPTH = 1024;       // Operand stack depth
    parameter int CALL_STACK_DEPTH = 256;   // Call stack depth
    parameter int LABEL_STACK_DEPTH = 256;  // Label/block stack depth
    parameter int LOCAL_COUNT = 256;        // Max locals per function
    parameter int MEMORY_PAGES = 65536;     // Max memory pages (64KB each) - WASM32 limit
    parameter int PAGE_SIZE = 65536;        // 64KB per page
    parameter int MAX_FUNCTIONS = 1024;     // Max functions in module
    parameter int MAX_GLOBALS = 256;        // Max globals
    parameter int MAX_TABLES = 16;          // Max tables

    // Table cache parameters
    parameter int TABLE_CACHE_SIZE = 16;    // 16-entry direct-mapped cache (4 per table)

    // =========================================================================
    // Table Cache Entry (for memory-backed tables with caching)
    // =========================================================================
    typedef struct packed {
        logic        valid;
        logic [1:0]  table_idx;
        logic [15:0] elem_idx;
        logic [31:0] data;
    } table_cache_entry_t;

    // =========================================================================
    // Stack Entry (128-bit value with type tag for SIMD support)
    // =========================================================================
    typedef struct packed {
        valtype_t    vtype;  // 4 bits
        logic [127:0] value; // 128 bits (upper 64 bits unused for non-SIMD types)
    } stack_entry_t;         // Total: 132 bits

    // =========================================================================
    // Label Entry (for block/loop/if control flow)
    // =========================================================================
    typedef struct packed {
        logic [31:0] target_pc;    // Branch target (continuation or loop start)
        logic [15:0] stack_height; // Stack height at block entry
        logic [7:0]  arity;        // Number of results
        logic        is_loop;      // True for loop (branch goes to start)
    } label_entry_t;

    // =========================================================================
    // Call Frame Entry
    // =========================================================================
    typedef struct packed {
        logic [31:0] return_pc;      // Return address
        logic [15:0] func_idx;       // Function index
        logic [15:0] local_base;     // Base index in local storage
        logic [15:0] stack_height;   // Stack height at call
        logic [7:0]  label_height;   // Label stack height at call
        logic [7:0]  arity;          // Number of return values
    } frame_entry_t;

    // =========================================================================
    // Function Entry (in function table)
    // =========================================================================
    typedef struct packed {
        logic [31:0] code_offset;    // Start offset in code memory
        logic [31:0] code_length;    // Length of function body
        logic [15:0] type_idx;       // Function type index
        logic [7:0]  param_count;    // Number of parameters
        logic [7:0]  result_count;   // Number of results
        logic [7:0]  local_count;    // Number of locals (excluding params)
    } func_entry_t;

    // =========================================================================
    // Global Entry (128-bit value for SIMD support)
    // =========================================================================
    typedef struct packed {
        valtype_t     vtype;
        logic         mutable_flag;
        logic [127:0] value;        // 128 bits (upper 64 bits unused for non-SIMD types)
    } global_entry_t;

    // =========================================================================
    // Decoded Instruction (128-bit immediate for SIMD v128.const)
    // =========================================================================
    typedef struct packed {
        opcode_t      opcode;
        logic [127:0] immediate;     // Immediate value (const, index, sub-opcode for SIMD)
        logic [127:0] immediate2;    // Second immediate (for memory ops: offset, v128.const: value)
        logic [7:0]   instr_length;  // Length of instruction in bytes
        logic         has_immediate;
        logic         has_immediate2;
    } decoded_instr_t;

    // =========================================================================
    // Helper Functions
    // =========================================================================

    // Count leading zeros for 32-bit
    function automatic logic [5:0] clz32(input logic [31:0] val);
        logic [5:0] count;
        count = 0;
        for (int i = 31; i >= 0; i--) begin
            if (val[i]) return 6'd31 - i[5:0];
        end
        return 6'd32;
    endfunction

    // Count leading zeros for 64-bit
    function automatic logic [6:0] clz64(input logic [63:0] val);
        logic [6:0] count;
        count = 0;
        for (int i = 63; i >= 0; i--) begin
            if (val[i]) return 7'd63 - i[6:0];
        end
        return 7'd64;
    endfunction

    // Count trailing zeros for 32-bit
    function automatic logic [5:0] ctz32(input logic [31:0] val);
        for (int i = 0; i < 32; i++) begin
            if (val[i]) return i[5:0];
        end
        return 6'd32;
    endfunction

    // Count trailing zeros for 64-bit
    function automatic logic [6:0] ctz64(input logic [63:0] val);
        for (int i = 0; i < 64; i++) begin
            if (val[i]) return i[6:0];
        end
        return 7'd64;
    endfunction

    // Population count for 32-bit
    function automatic logic [5:0] popcnt32(input logic [31:0] val);
        logic [5:0] count;
        count = 0;
        for (int i = 0; i < 32; i++) begin
            count = count + {5'b0, val[i]};
        end
        return count;
    endfunction

    // Population count for 64-bit
    function automatic logic [6:0] popcnt64(input logic [63:0] val);
        logic [6:0] count;
        count = 0;
        for (int i = 0; i < 64; i++) begin
            count = count + {6'b0, val[i]};
        end
        return count;
    endfunction

    // Rotate left 32-bit
    function automatic logic [31:0] rotl32(input logic [31:0] val, input logic [4:0] amt);
        return (val << amt) | (val >> (32 - amt));
    endfunction

    // Rotate right 32-bit
    function automatic logic [31:0] rotr32(input logic [31:0] val, input logic [4:0] amt);
        return (val >> amt) | (val << (32 - amt));
    endfunction

    // Rotate left 64-bit
    function automatic logic [63:0] rotl64(input logic [63:0] val, input logic [5:0] amt);
        return (val << amt) | (val >> (64 - amt));
    endfunction

    // Rotate right 64-bit
    function automatic logic [63:0] rotr64(input logic [63:0] val, input logic [5:0] amt);
        return (val >> amt) | (val << (64 - amt));
    endfunction

endpackage
