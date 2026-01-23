// WebAssembly Instruction Decoder
// Decodes binary WebAssembly instructions and extracts immediates

module wasm_decoder
    import wasm_pkg::*;
(
    input  logic        clk,
    input  logic        rst_n,

    // Input: instruction bytes from code memory
    input  logic        valid_in,
    input  logic [31:0] pc,
    input  logic [7:0]  instr_bytes [0:19],  // Up to 20 bytes lookahead (for v128.const)
    input  logic [4:0]  bytes_available,

    // Output: decoded instruction
    output logic        valid_out,
    output decoded_instr_t decoded,
    output logic [31:0] next_pc
);

    // LEB128 decoder for unsigned integers
    function automatic logic [63:0] decode_uleb128(
        input logic [7:0] bytes [0:9],
        output logic [3:0] length
    );
        logic [63:0] result;
        logic [6:0] shift;
        result = 64'h0;
        shift = 7'h0;
        length = 4'h0;

        for (int i = 0; i < 10; i++) begin
            result = result | ((bytes[i] & 8'h7F) << shift);
            length = length + 1;
            if ((bytes[i] & 8'h80) == 0) begin
                return result;
            end
            shift = shift + 7;
        end
        return result;
    endfunction

    // LEB128 decoder for signed integers
    function automatic logic [63:0] decode_sleb128(
        input logic [7:0] bytes [0:9],
        input int max_bits,
        output logic [3:0] length
    );
        logic [63:0] result;
        logic [6:0] shift;
        logic [7:0] byte_val;
        result = 64'h0;
        shift = 7'h0;
        length = 4'h0;

        for (int i = 0; i < 10; i++) begin
            byte_val = bytes[i];
            result = result | ((byte_val & 8'h7F) << shift);
            shift = shift + 7;
            length = length + 1;
            if ((byte_val & 8'h80) == 0) begin
                // Sign extend if negative
                if ((shift < max_bits) && (byte_val & 8'h40)) begin
                    result = result | (~64'h0 << shift);
                end
                return result;
            end
        end
        return result;
    endfunction

    // Main decode logic
    always_comb begin
        decoded = '0;
        valid_out = 1'b0;
        next_pc = pc;

        if (valid_in && bytes_available > 0) begin
            valid_out = 1'b1;
            decoded.opcode = opcode_t'(instr_bytes[0]);
            decoded.instr_length = 8'd1;
            decoded.has_immediate = 1'b0;
            decoded.has_immediate2 = 1'b0;

            case (instr_bytes[0])
                // No immediate instructions
                8'h00, 8'h01, 8'h0B, 8'h0F,  // unreachable, nop, end, return
                8'h1A, 8'h1B,                 // drop, select (untyped)
                8'h45, 8'h46, 8'h47, 8'h48, 8'h49, 8'h4A, 8'h4B, 8'h4C, 8'h4D, 8'h4E, 8'h4F,  // i32 comparisons
                8'h50, 8'h51, 8'h52, 8'h53, 8'h54, 8'h55, 8'h56, 8'h57, 8'h58, 8'h59, 8'h5A,  // i64 comparisons
                8'h5B, 8'h5C, 8'h5D, 8'h5E, 8'h5F, 8'h60,  // f32 comparisons
                8'h61, 8'h62, 8'h63, 8'h64, 8'h65, 8'h66,  // f64 comparisons
                8'h67, 8'h68, 8'h69, 8'h6A, 8'h6B, 8'h6C, 8'h6D, 8'h6E, 8'h6F,  // i32 arithmetic
                8'h70, 8'h71, 8'h72, 8'h73, 8'h74, 8'h75, 8'h76, 8'h77, 8'h78,  // i32 bitwise
                8'h79, 8'h7A, 8'h7B, 8'h7C, 8'h7D, 8'h7E, 8'h7F, 8'h80, 8'h81, 8'h82,  // i64 arithmetic
                8'h83, 8'h84, 8'h85, 8'h86, 8'h87, 8'h88, 8'h89, 8'h8A,  // i64 bitwise
                8'h8B, 8'h8C, 8'h8D, 8'h8E, 8'h8F, 8'h90, 8'h91, 8'h92, 8'h93, 8'h94, 8'h95, 8'h96, 8'h97, 8'h98,  // f32 ops
                8'h99, 8'h9A, 8'h9B, 8'h9C, 8'h9D, 8'h9E, 8'h9F, 8'hA0, 8'hA1, 8'hA2, 8'hA3, 8'hA4, 8'hA5, 8'hA6,  // f64 ops
                8'hA7, 8'hA8, 8'hA9, 8'hAA, 8'hAB, 8'hAC, 8'hAD, 8'hAE, 8'hAF,  // conversions
                8'hB0, 8'hB1, 8'hB2, 8'hB3, 8'hB4, 8'hB5, 8'hB6, 8'hB7, 8'hB8, 8'hB9, 8'hBA, 8'hBB, 8'hBC, 8'hBD, 8'hBE, 8'hBF,
                8'hC0, 8'hC1, 8'hC2, 8'hC3, 8'hC4: begin  // sign extensions
                    decoded.instr_length = 8'd1;
                end

                // Block-type immediate (block, loop, if)
                8'h02, 8'h03, 8'h04: begin
                    logic [3:0] len;
                    logic [7:0] type_byte;
                    logic [7:0] leb_bytes [0:9];

                    // Get bytes for LEB128 decode
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end

                    type_byte = instr_bytes[1];

                    // Block type encoding:
                    // 0x40 = empty (void)
                    // 0x7F = i32, 0x7E = i64, 0x7D = f32, 0x7C = f64
                    // 0x70 = funcref, 0x6F = externref
                    // 0x63 = ref null t, 0x64 = ref t (followed by heaptype)
                    // Otherwise it's a type index (s33 LEB128)

                    if (type_byte == 8'h40) begin
                        // Empty block type
                        decoded.immediate = 128'hFFFFFFFF;  // Marker for void
                        decoded.instr_length = 8'd2;
                    end else if (type_byte >= 8'h7B && type_byte <= 8'h7F) begin
                        // Single value type (i32/i64/f32/f64/v128)
                        // 0x7F=i32, 0x7E=i64, 0x7D=f32, 0x7C=f64, 0x7B=v128
                        decoded.immediate = {120'b0, type_byte};
                        decoded.instr_length = 8'd2;
                    end else if (type_byte == 8'h70 || type_byte == 8'h6F) begin
                        // Reference type (funcref or externref)
                        decoded.immediate = {120'b0, type_byte};
                        decoded.instr_length = 8'd2;
                    end else if (type_byte == 8'h63 || type_byte == 8'h64) begin
                        // Typed reference: ref null t (0x63) or ref t (0x64)
                        // Followed by heaptype LEB128
                        logic [3:0] ht_len;
                        logic [7:0] ht_bytes [0:9];
                        for (int i = 0; i < 10; i++) begin
                            ht_bytes[i] = instr_bytes[i+2];  // Start after type_byte
                        end
                        decoded.immediate = decode_sleb128(ht_bytes, 33, ht_len);
                        decoded.instr_length = 8'd2 + {4'b0, ht_len};  // opcode + type_byte + heaptype
                    end else begin
                        // Type index (treat as unsigned for now)
                        decoded.immediate = decode_uleb128(leb_bytes, len);
                        decoded.instr_length = 8'd1 + {4'b0, len};
                    end
                    decoded.has_immediate = 1'b1;
                end

                // Branch label index (br, br_if)
                8'h0C, 8'h0D: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // br_table - complex, has multiple immediates
                // Format: 0x0E <count> <targets[0..count]> <default>
                // immediate = count of targets
                // immediate2 = offset to first target (1 + len_of_count)
                8'h0E: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len);
                    decoded.immediate2 = {28'b0, len};  // Offset to first target from opcode
                    decoded.instr_length = 8'd1 + {4'b0, len};  // Partial - execution handles full skip
                    decoded.has_immediate = 1'b1;
                    decoded.has_immediate2 = 1'b1;
                end

                // select_t (typed select) - has count + type vector
                // Format: 0x1C + count (LEB128) + count × valtype (each 1 byte)
                8'h1C: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    logic [63:0] count;
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    count = decode_uleb128(leb_bytes, len);
                    // Length = 1 (opcode) + len (count LEB) + count (type bytes)
                    decoded.instr_length = 8'd1 + {4'b0, len} + count[7:0];
                    // We don't actually need the type info since we track types
                end

                // Function index (call)
                8'h10: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // call_indirect - type index and table index
                8'h11: begin
                    logic [3:0] len1, len2;
                    logic [7:0] leb_bytes [0:9];

                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len1);

                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1+len1];
                    end
                    decoded.immediate2 = decode_uleb128(leb_bytes, len2);

                    decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2};
                    decoded.has_immediate = 1'b1;
                    decoded.has_immediate2 = 1'b1;
                end

                // Local/global variable index
                8'h20, 8'h21, 8'h22, 8'h23, 8'h24: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // Table operations - table.get and table.set
                // immediate = table index
                8'h25, 8'h26: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // Memory instructions - have align and offset
                8'h28, 8'h29, 8'h2A, 8'h2B, 8'h2C, 8'h2D, 8'h2E, 8'h2F,
                8'h30, 8'h31, 8'h32, 8'h33, 8'h34, 8'h35,
                8'h36, 8'h37, 8'h38, 8'h39, 8'h3A, 8'h3B, 8'h3C, 8'h3D, 8'h3E: begin
                    logic [3:0] len1, len2;
                    logic [7:0] leb_bytes [0:9];

                    // Alignment
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len1);

                    // Offset
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1+len1];
                    end
                    decoded.immediate2 = decode_uleb128(leb_bytes, len2);

                    decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2};
                    decoded.has_immediate = 1'b1;
                    decoded.has_immediate2 = 1'b1;
                end

                // memory.size and memory.grow - memory index (usually 0x00)
                8'h3F, 8'h40: begin
                    decoded.immediate = {56'b0, instr_bytes[1]};
                    decoded.instr_length = 8'd2;
                    decoded.has_immediate = 1'b1;
                end

                // i32.const
                8'h41: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_sleb128(leb_bytes, 32, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // i64.const
                8'h42: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_sleb128(leb_bytes, 64, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // f32.const - 4 byte IEEE 754
                8'h43: begin
                    decoded.immediate = {32'b0, instr_bytes[4], instr_bytes[3], instr_bytes[2], instr_bytes[1]};
                    decoded.instr_length = 8'd5;
                    decoded.has_immediate = 1'b1;
                end

                // f64.const - 8 byte IEEE 754
                8'h44: begin
                    decoded.immediate = {instr_bytes[8], instr_bytes[7], instr_bytes[6], instr_bytes[5],
                                         instr_bytes[4], instr_bytes[3], instr_bytes[2], instr_bytes[1]};
                    decoded.instr_length = 8'd9;
                    decoded.has_immediate = 1'b1;
                end

                // else marker
                8'h05: begin
                    decoded.instr_length = 8'd1;
                end

                // Extended opcodes (0xFC prefix)
                // Format: 0xFC <sub_opcode:LEB128> [immediates...]
                // immediate = sub-opcode, immediate2 = first operand (if any)
                8'hFC: begin
                    logic [3:0] len1, len2, len3;
                    logic [7:0] leb_bytes [0:9];
                    logic [63:0] sub_opcode;

                    // Decode sub-opcode (LEB128 encoded)
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    sub_opcode = decode_uleb128(leb_bytes, len1);
                    decoded.immediate = sub_opcode;
                    decoded.has_immediate = 1'b1;

                    case (sub_opcode[7:0])
                        // Saturating truncation (no additional immediates)
                        8'h00, 8'h01, 8'h02, 8'h03,
                        8'h04, 8'h05, 8'h06, 8'h07: begin
                            decoded.instr_length = 8'd1 + {4'b0, len1};
                        end

                        // memory.init - data_idx + mem_idx (usually 0)
                        8'h08: begin
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            decoded.immediate2 = decode_uleb128(leb_bytes, len2);  // data_idx
                            // Skip mem_idx (always 0 for now)
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2} + 8'd1;
                            decoded.has_immediate2 = 1'b1;
                        end

                        // data.drop - data_idx
                        8'h09: begin
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            decoded.immediate2 = decode_uleb128(leb_bytes, len2);
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2};
                            decoded.has_immediate2 = 1'b1;
                        end

                        // memory.copy - dst_mem + src_mem (both usually 0)
                        8'h0A: begin
                            decoded.instr_length = 8'd1 + {4'b0, len1} + 8'd2;  // +2 for two 0x00 bytes
                        end

                        // memory.fill - mem_idx (usually 0)
                        8'h0B: begin
                            decoded.instr_length = 8'd1 + {4'b0, len1} + 8'd1;  // +1 for 0x00
                        end

                        // table.init - elem_idx + table_idx
                        // immediate2[15:0] = elem_idx, immediate2[31:16] = table_idx
                        8'h0C: begin
                            logic [63:0] elem_idx_val, table_idx_val;
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            elem_idx_val = decode_uleb128(leb_bytes, len2);
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1+len2];
                            end
                            table_idx_val = decode_uleb128(leb_bytes, len3);
                            decoded.immediate2 = {table_idx_val[15:0], elem_idx_val[15:0]};
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2} + {4'b0, len3};
                            decoded.has_immediate2 = 1'b1;
                        end

                        // elem.drop - elem_idx
                        8'h0D: begin
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            decoded.immediate2 = decode_uleb128(leb_bytes, len2);
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2};
                            decoded.has_immediate2 = 1'b1;
                        end

                        // table.copy - dst_table_idx + src_table_idx
                        // immediate2[15:0] = dst_table, immediate2[31:16] = src_table
                        8'h0E: begin
                            logic [63:0] dst_table_val, src_table_val;
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            dst_table_val = decode_uleb128(leb_bytes, len2);
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1+len2];
                            end
                            src_table_val = decode_uleb128(leb_bytes, len3);
                            decoded.immediate2 = {src_table_val[15:0], dst_table_val[15:0]};
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2} + {4'b0, len3};
                            decoded.has_immediate2 = 1'b1;
                        end

                        // table.grow, table.size, table.fill - table_idx
                        8'h0F, 8'h10, 8'h11: begin
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            decoded.immediate2 = decode_uleb128(leb_bytes, len2);
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2};
                            decoded.has_immediate2 = 1'b1;
                        end

                        default: begin
                            // Unknown extended opcode
                            decoded.instr_length = 8'd1 + {4'b0, len1};
                        end
                    endcase
                end

                // Reference type instructions (0xD0 - 0xD6)
                // ref.null t - push null reference of type t
                // immediate = heap type (0x70 = funcref, 0x6F = externref)
                8'hD0: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_sleb128(leb_bytes, 33, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // ref.is_null - check if reference is null
                8'hD1: begin
                    decoded.instr_length = 8'd1;
                end

                // ref.func $funcidx - create funcref from function index
                8'hD2: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // ref.as_non_null - assert reference is not null
                8'hD3: begin
                    decoded.instr_length = 8'd1;
                end

                // br_on_null $l - branch if reference is null
                8'hD5: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = decode_uleb128(leb_bytes, len);
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // br_on_non_null $l - branch if reference is not null
                8'hD6: begin
                    logic [3:0] len;
                    logic [7:0] leb_bytes [0:9];
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    decoded.immediate = {64'b0, decode_uleb128(leb_bytes, len)};
                    decoded.instr_length = 8'd1 + {4'b0, len};
                    decoded.has_immediate = 1'b1;
                end

                // SIMD opcodes (0xFD prefix)
                // Format: 0xFD <sub_opcode:LEB128> [immediates...]
                // immediate[8:0] = sub-opcode, immediate2 = offset for memory ops
                // For v128.const: immediate[127:0] = the 128-bit constant value
                8'hFD: begin
                    logic [3:0] len1, len2, len3;
                    logic [7:0] leb_bytes [0:9];
                    logic [63:0] sub_opcode;

                    // Decode sub-opcode (LEB128 encoded)
                    for (int i = 0; i < 10; i++) begin
                        leb_bytes[i] = instr_bytes[i+1];
                    end
                    sub_opcode = decode_uleb128(leb_bytes, len1);
                    decoded.has_immediate = 1'b1;

                    case (sub_opcode[8:0])
                        // v128.load, v128.store - memarg (align + offset)
                        9'h000, 9'h00B: begin
                            // v128.load (0x00), v128.store (0x0B)
                            decoded.immediate = {119'b0, sub_opcode[8:0]};
                            // Decode align (skip it) and offset
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            decode_uleb128(leb_bytes, len2);  // align (ignored)
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1+len2];
                            end
                            decoded.immediate2 = decode_uleb128(leb_bytes, len3);  // offset
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2} + {4'b0, len3};
                            decoded.has_immediate2 = 1'b1;
                        end

                        // v128.loadNxM_s/u, v128.loadN_splat, v128.loadN_zero
                        9'h001, 9'h002, 9'h003, 9'h004, 9'h005, 9'h006,  // load extend
                        9'h007, 9'h008, 9'h009, 9'h00A,                   // load splat
                        9'h05C, 9'h05D: begin                             // load zero
                            decoded.immediate = {119'b0, sub_opcode[8:0]};
                            // Decode memarg
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            decode_uleb128(leb_bytes, len2);  // align
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1+len2];
                            end
                            decoded.immediate2 = decode_uleb128(leb_bytes, len3);  // offset
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2} + {4'b0, len3};
                            decoded.has_immediate2 = 1'b1;
                        end

                        // v128.const - 16 bytes of immediate data
                        9'h00C: begin
                            // Store sub-opcode in immediate[8:0] for consistent dispatch
                            decoded.immediate = {119'b0, 9'h00C};
                            // Read 16 bytes in little-endian order into immediate2
                            decoded.immediate2 = {instr_bytes[1+len1+15], instr_bytes[1+len1+14],
                                                  instr_bytes[1+len1+13], instr_bytes[1+len1+12],
                                                  instr_bytes[1+len1+11], instr_bytes[1+len1+10],
                                                  instr_bytes[1+len1+9],  instr_bytes[1+len1+8],
                                                  instr_bytes[1+len1+7],  instr_bytes[1+len1+6],
                                                  instr_bytes[1+len1+5],  instr_bytes[1+len1+4],
                                                  instr_bytes[1+len1+3],  instr_bytes[1+len1+2],
                                                  instr_bytes[1+len1+1],  instr_bytes[1+len1]};
                            decoded.instr_length = 8'd1 + {4'b0, len1} + 8'd16;
                            decoded.has_immediate2 = 1'b1;
                        end

                        // i8x16.shuffle - 16 lane indices
                        9'h00D: begin
                            // Store sub-opcode in immediate[8:0] for consistent dispatch
                            decoded.immediate = {119'b0, 9'h00D};
                            // Read 16 lane indices into immediate2
                            decoded.immediate2 = {instr_bytes[1+len1+15], instr_bytes[1+len1+14],
                                                 instr_bytes[1+len1+13], instr_bytes[1+len1+12],
                                                 instr_bytes[1+len1+11], instr_bytes[1+len1+10],
                                                 instr_bytes[1+len1+9],  instr_bytes[1+len1+8],
                                                 instr_bytes[1+len1+7],  instr_bytes[1+len1+6],
                                                 instr_bytes[1+len1+5],  instr_bytes[1+len1+4],
                                                 instr_bytes[1+len1+3],  instr_bytes[1+len1+2],
                                                 instr_bytes[1+len1+1],  instr_bytes[1+len1]};
                            decoded.instr_length = 8'd1 + {4'b0, len1} + 8'd16;
                            decoded.has_immediate2 = 1'b1;
                        end

                        // Lane extract/replace operations - single lane index byte
                        9'h015, 9'h016, 9'h017,  // i8x16 extract/replace
                        9'h018, 9'h019, 9'h01A,  // i16x8 extract/replace
                        9'h01B, 9'h01C,          // i32x4 extract/replace
                        9'h01D, 9'h01E,          // i64x2 extract/replace
                        9'h01F, 9'h020,          // f32x4 extract/replace
                        9'h021, 9'h022: begin    // f64x2 extract/replace
                            decoded.immediate = {111'b0, instr_bytes[1+len1], sub_opcode[8:0]};
                            decoded.instr_length = 8'd1 + {4'b0, len1} + 8'd1;
                        end

                        // v128.loadN_lane, v128.storeN_lane - memarg + laneidx
                        9'h054, 9'h055, 9'h056, 9'h057,  // load lane
                        9'h058, 9'h059, 9'h05A, 9'h05B: begin  // store lane
                            decoded.immediate = {119'b0, sub_opcode[8:0]};
                            // Decode memarg
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1];
                            end
                            decode_uleb128(leb_bytes, len2);  // align
                            for (int i = 0; i < 10; i++) begin
                                leb_bytes[i] = instr_bytes[i+1+len1+len2];
                            end
                            decoded.immediate2 = decode_uleb128(leb_bytes, len3);  // offset
                            // Lane index is after offset
                            decoded.immediate2[15:8] = instr_bytes[1+len1+len2+len3];  // laneidx
                            decoded.instr_length = 8'd1 + {4'b0, len1} + {4'b0, len2} + {4'b0, len3} + 8'd1;
                            decoded.has_immediate2 = 1'b1;
                        end

                        // All other SIMD operations - no immediates beyond sub-opcode
                        default: begin
                            decoded.immediate = {119'b0, sub_opcode[8:0]};
                            decoded.instr_length = 8'd1 + {4'b0, len1};
                        end
                    endcase
                end

                default: begin
                    // Unknown opcode - single byte
                    decoded.instr_length = 8'd1;
                end
            endcase

            next_pc = pc + {24'b0, decoded.instr_length};
        end
    end

endmodule
