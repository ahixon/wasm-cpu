// WebAssembly Module Loader
// Parses a WASM binary module and extracts function information
// for the CPU to execute

module wasm_loader
    import wasm_pkg::*;
(
    input  logic        clk,
    input  logic        rst_n,

    // Control
    input  logic        load_start,
    input  logic [31:0] module_size,  // Size of WASM module in bytes
    output logic        load_done,
    output logic        load_error,

    // Module memory interface (read)
    output logic [31:0] mem_addr,
    input  logic [7:0]  mem_data,

    // Code memory interface (write)
    output logic        code_wr_en,
    output logic [31:0] code_wr_addr,
    output logic [7:0]  code_wr_data,

    // Function table interface (write)
    output logic        func_wr_en,
    output logic [15:0] func_wr_idx,
    output func_entry_t func_wr_data,

    // Info about loaded module
    output logic [15:0] num_functions,
    output logic [31:0] start_func_idx  // -1 if no start function
);

    // WASM section IDs
    localparam SEC_CUSTOM   = 8'd0;
    localparam SEC_TYPE     = 8'd1;
    localparam SEC_IMPORT   = 8'd2;
    localparam SEC_FUNCTION = 8'd3;
    localparam SEC_TABLE    = 8'd4;
    localparam SEC_MEMORY   = 8'd5;
    localparam SEC_GLOBAL   = 8'd6;
    localparam SEC_EXPORT   = 8'd7;
    localparam SEC_START    = 8'd8;
    localparam SEC_ELEMENT  = 8'd9;
    localparam SEC_CODE     = 8'd10;
    localparam SEC_DATA     = 8'd11;

    // State machine
    typedef enum logic [3:0] {
        S_IDLE,
        S_CHECK_MAGIC,
        S_CHECK_VERSION,
        S_READ_SECTION_ID,
        S_READ_SECTION_SIZE,
        S_SKIP_SECTION,
        S_PARSE_TYPE_SECTION,
        S_PARSE_FUNC_SECTION,
        S_PARSE_CODE_SECTION,
        S_COPY_CODE,
        S_DONE,
        S_ERROR
    } state_t;

    state_t state, next_state;

    // Counters and registers
    logic [31:0] pos;           // Current position in module
    logic [31:0] section_end;   // End of current section
    logic [7:0]  section_id;
    logic [31:0] section_size;
    logic [31:0] leb_value;
    logic [4:0]  leb_shift;
    logic [31:0] code_offset;   // Where to write next code byte
    logic [15:0] func_count;    // Number of functions
    logic [15:0] current_func;  // Current function being processed
    logic [31:0] func_body_size;
    logic [31:0] local_count;
    logic [31:0] bytes_to_copy;

    // Type information storage (simplified)
    logic [7:0] type_param_counts [0:255];
    logic [7:0] type_result_counts [0:255];
    logic [15:0] num_types;

    // Function type indices
    logic [7:0] func_type_indices [0:255];

    // Byte buffer for multi-byte reads
    logic [7:0] byte_buf [0:7];
    logic [2:0] byte_idx;

    // LEB128 decoder state
    logic leb_done;
    logic [31:0] leb_result;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_IDLE;
            pos <= 0;
            load_done <= 0;
            load_error <= 0;
            code_wr_en <= 0;
            func_wr_en <= 0;
            num_functions <= 0;
            start_func_idx <= 32'hFFFFFFFF;
            code_offset <= 0;
            func_count <= 0;
            current_func <= 0;
            num_types <= 0;
        end else begin
            // Default outputs
            code_wr_en <= 0;
            func_wr_en <= 0;

            case (state)
                S_IDLE: begin
                    if (load_start) begin
                        pos <= 0;
                        load_done <= 0;
                        load_error <= 0;
                        code_offset <= 0;
                        func_count <= 0;
                        current_func <= 0;
                        num_types <= 0;
                        byte_idx <= 0;
                        state <= S_CHECK_MAGIC;
                    end
                end

                S_CHECK_MAGIC: begin
                    // Read 4 bytes: 0x00 0x61 0x73 0x6D
                    mem_addr <= pos;
                    if (byte_idx < 4) begin
                        byte_buf[byte_idx] <= mem_data;
                        byte_idx <= byte_idx + 1;
                        pos <= pos + 1;
                    end else begin
                        if (byte_buf[0] == 8'h00 && byte_buf[1] == 8'h61 &&
                            byte_buf[2] == 8'h73 && byte_buf[3] == 8'h6D) begin
                            byte_idx <= 0;
                            state <= S_CHECK_VERSION;
                        end else begin
                            state <= S_ERROR;
                        end
                    end
                end

                S_CHECK_VERSION: begin
                    // Read 4 bytes: 0x01 0x00 0x00 0x00
                    mem_addr <= pos;
                    if (byte_idx < 4) begin
                        byte_buf[byte_idx] <= mem_data;
                        byte_idx <= byte_idx + 1;
                        pos <= pos + 1;
                    end else begin
                        if (byte_buf[0] == 8'h01 && byte_buf[1] == 8'h00 &&
                            byte_buf[2] == 8'h00 && byte_buf[3] == 8'h00) begin
                            byte_idx <= 0;
                            state <= S_READ_SECTION_ID;
                        end else begin
                            state <= S_ERROR;
                        end
                    end
                end

                S_READ_SECTION_ID: begin
                    if (pos >= module_size) begin
                        // End of module
                        num_functions <= func_count;
                        state <= S_DONE;
                    end else begin
                        mem_addr <= pos;
                        section_id <= mem_data;
                        pos <= pos + 1;
                        leb_value <= 0;
                        leb_shift <= 0;
                        state <= S_READ_SECTION_SIZE;
                    end
                end

                S_READ_SECTION_SIZE: begin
                    // Read LEB128 section size
                    mem_addr <= pos;
                    leb_value <= leb_value | ((mem_data & 8'h7F) << leb_shift);
                    pos <= pos + 1;
                    if ((mem_data & 8'h80) == 0) begin
                        section_size <= leb_value | ((mem_data & 8'h7F) << leb_shift);
                        section_end <= pos + (leb_value | ((mem_data & 8'h7F) << leb_shift));

                        case (section_id)
                            SEC_TYPE: state <= S_PARSE_TYPE_SECTION;
                            SEC_FUNCTION: state <= S_PARSE_FUNC_SECTION;
                            SEC_CODE: state <= S_PARSE_CODE_SECTION;
                            default: state <= S_SKIP_SECTION;
                        endcase

                        leb_value <= 0;
                        leb_shift <= 0;
                    end else begin
                        leb_shift <= leb_shift + 7;
                    end
                end

                S_SKIP_SECTION: begin
                    // Skip unknown sections
                    pos <= section_end;
                    state <= S_READ_SECTION_ID;
                end

                S_PARSE_TYPE_SECTION: begin
                    // Simplified: just skip to next section
                    // In a full implementation, we'd parse function signatures
                    pos <= section_end;
                    state <= S_READ_SECTION_ID;
                end

                S_PARSE_FUNC_SECTION: begin
                    // Simplified: just skip to next section
                    // This section contains type indices for each function
                    pos <= section_end;
                    state <= S_READ_SECTION_ID;
                end

                S_PARSE_CODE_SECTION: begin
                    // Read function count
                    mem_addr <= pos;
                    leb_value <= leb_value | ((mem_data & 8'h7F) << leb_shift);
                    pos <= pos + 1;
                    if ((mem_data & 8'h80) == 0) begin
                        func_count <= leb_value | ((mem_data & 8'h7F) << leb_shift);
                        current_func <= 0;
                        leb_value <= 0;
                        leb_shift <= 0;
                        state <= S_COPY_CODE;
                    end else begin
                        leb_shift <= leb_shift + 7;
                    end
                end

                S_COPY_CODE: begin
                    if (current_func >= func_count) begin
                        num_functions <= func_count;
                        state <= S_READ_SECTION_ID;
                    end else if (leb_shift == 0 && bytes_to_copy == 0) begin
                        // Read function body size (LEB128)
                        mem_addr <= pos;
                        leb_value <= leb_value | ((mem_data & 8'h7F) << leb_shift);
                        pos <= pos + 1;
                        if ((mem_data & 8'h80) == 0) begin
                            func_body_size <= leb_value | ((mem_data & 8'h7F) << leb_shift);
                            bytes_to_copy <= leb_value | ((mem_data & 8'h7F) << leb_shift);

                            // Register the function
                            func_wr_en <= 1;
                            func_wr_idx <= current_func;
                            func_wr_data.code_offset <= code_offset;
                            func_wr_data.code_length <= leb_value | ((mem_data & 8'h7F) << leb_shift);
                            func_wr_data.type_idx <= 0;
                            func_wr_data.param_count <= 0;
                            func_wr_data.result_count <= 1;
                            func_wr_data.local_count <= 0;

                            leb_value <= 0;
                            leb_shift <= 5'd31; // Signal to start copying
                        end else begin
                            leb_shift <= leb_shift + 7;
                        end
                    end else if (bytes_to_copy > 0) begin
                        // Copy function body to code memory
                        mem_addr <= pos;
                        code_wr_en <= 1;
                        code_wr_addr <= code_offset;
                        code_wr_data <= mem_data;
                        code_offset <= code_offset + 1;
                        pos <= pos + 1;
                        bytes_to_copy <= bytes_to_copy - 1;

                        if (bytes_to_copy == 1) begin
                            current_func <= current_func + 1;
                            leb_value <= 0;
                            leb_shift <= 0;
                        end
                    end
                end

                S_DONE: begin
                    load_done <= 1;
                end

                S_ERROR: begin
                    load_error <= 1;
                    load_done <= 1;
                end
            endcase
        end
    end

endmodule
