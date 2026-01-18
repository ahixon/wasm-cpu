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

        // Prefix for extended opcodes
        OP_PREFIX_FC      = 8'hFC,
        OP_PREFIX_FD      = 8'hFD
    } opcode_t;

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
    // Memory Operation Types
    // =========================================================================
    typedef enum logic [3:0] {
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
        MEM_STORE_I32_FROM_I64
    } mem_op_t;

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
        STATE_TRAP,
        STATE_HALT
    } exec_state_t;

    // =========================================================================
    // Trap Types
    // =========================================================================
    typedef enum logic [3:0] {
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
        TRAP_CALL_STACK_EXHAUSTED
    } trap_t;

    // =========================================================================
    // Configuration Parameters
    // =========================================================================
    parameter int STACK_DEPTH = 1024;       // Operand stack depth
    parameter int CALL_STACK_DEPTH = 256;   // Call stack depth
    parameter int LABEL_STACK_DEPTH = 256;  // Label/block stack depth
    parameter int LOCAL_COUNT = 256;        // Max locals per function
    parameter int MEMORY_PAGES = 256;       // Max memory pages (64KB each)
    parameter int PAGE_SIZE = 65536;        // 64KB per page
    parameter int MAX_FUNCTIONS = 1024;     // Max functions in module
    parameter int MAX_GLOBALS = 256;        // Max globals
    parameter int MAX_TABLES = 16;          // Max tables

    // =========================================================================
    // Stack Entry (64-bit value with type tag)
    // =========================================================================
    typedef struct packed {
        valtype_t  vtype;    // 4 bits
        logic [63:0] value;  // 64 bits
    } stack_entry_t;         // Total: 68 bits

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
    // Global Entry
    // =========================================================================
    typedef struct packed {
        valtype_t    vtype;
        logic        mutable_flag;
        logic [63:0] value;
    } global_entry_t;

    // =========================================================================
    // Decoded Instruction
    // =========================================================================
    typedef struct packed {
        opcode_t     opcode;
        logic [63:0] immediate;      // Immediate value (const, index, etc.)
        logic [31:0] immediate2;     // Second immediate (for memory ops: offset)
        logic [7:0]  instr_length;   // Length of instruction in bytes
        logic        has_immediate;
        logic        has_immediate2;
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
