//==============================================================================
// wasm_axi_lite_adapter.sv - AXI4-Lite Adapter for WASM Memory Interface
//
// Bridges the WASM memory bus interface (mem_bus_req_t/mem_bus_resp_t) to
// AXI4-Lite for connecting to external memory controllers (SDRAM, etc.)
//
// Features:
// - Supports 1/2/4/8 byte accesses
// - Single outstanding transaction (no pipelining)
// - Base address offset for memory-mapped placement
//
// Note: The WASM-specific management interface (init/grow) is NOT handled by
// this adapter - those operations must be handled by higher-level logic.
//==============================================================================

module wasm_axi_lite_adapter
  import wasm_pkg::*;
#(
  parameter logic [31:0] BASE_ADDR = 32'h0000_0000,  // AXI address offset
  parameter int          ADDR_WIDTH = 32,
  parameter int          DATA_WIDTH = 64            // Must match mem_bus_req_t
) (
  input  logic        clk_i,
  input  logic        rst_ni,

  // WASM memory bus interface (from CPU)
  input  mem_bus_req_t  wasm_req_i,
  output mem_bus_resp_t wasm_resp_o,

  // AXI4-Lite Master Interface
  // Write address channel
  output logic [ADDR_WIDTH-1:0] m_axi_awaddr,
  output logic [2:0]            m_axi_awprot,
  output logic                  m_axi_awvalid,
  input  logic                  m_axi_awready,

  // Write data channel
  output logic [DATA_WIDTH-1:0] m_axi_wdata,
  output logic [DATA_WIDTH/8-1:0] m_axi_wstrb,
  output logic                  m_axi_wvalid,
  input  logic                  m_axi_wready,

  // Write response channel
  input  logic [1:0]            m_axi_bresp,
  input  logic                  m_axi_bvalid,
  output logic                  m_axi_bready,

  // Read address channel
  output logic [ADDR_WIDTH-1:0] m_axi_araddr,
  output logic [2:0]            m_axi_arprot,
  output logic                  m_axi_arvalid,
  input  logic                  m_axi_arready,

  // Read data channel
  input  logic [DATA_WIDTH-1:0] m_axi_rdata,
  input  logic [1:0]            m_axi_rresp,
  input  logic                  m_axi_rvalid,
  output logic                  m_axi_rready
);

  //============================================================================
  // State Machine
  //============================================================================

  typedef enum logic [2:0] {
    ST_IDLE,
    ST_WRITE_ADDR,
    ST_WRITE_DATA,
    ST_WRITE_RESP,
    ST_READ_ADDR,
    ST_READ_DATA
  } state_t;

  state_t state_q, state_d;

  // Latched request
  logic        req_write_q;
  logic [31:0] req_addr_q;
  mem_size_t   req_size_q;
  logic [63:0] req_wdata_q;

  //============================================================================
  // Write Strobe Generation
  //============================================================================

  function automatic logic [7:0] gen_wstrb(mem_size_t size, logic [2:0] addr_offset);
    logic [7:0] base_strb;
    case (size)
      MEM_SIZE_1: base_strb = 8'b0000_0001;
      MEM_SIZE_2: base_strb = 8'b0000_0011;
      MEM_SIZE_4: base_strb = 8'b0000_1111;
      MEM_SIZE_8: base_strb = 8'b1111_1111;
      default:    base_strb = 8'b0000_1111;
    endcase
    // Shift strobe based on byte address offset within 64-bit word
    return base_strb << addr_offset;
  endfunction

  //============================================================================
  // State Machine Logic
  //============================================================================

  always_comb begin
    state_d = state_q;

    case (state_q)
      ST_IDLE: begin
        if (wasm_req_i.valid) begin
          if (wasm_req_i.write) begin
            state_d = ST_WRITE_ADDR;
          end else begin
            state_d = ST_READ_ADDR;
          end
        end
      end

      ST_WRITE_ADDR: begin
        if (m_axi_awready) begin
          state_d = ST_WRITE_DATA;
        end
      end

      ST_WRITE_DATA: begin
        if (m_axi_wready) begin
          state_d = ST_WRITE_RESP;
        end
      end

      ST_WRITE_RESP: begin
        if (m_axi_bvalid) begin
          state_d = ST_IDLE;
        end
      end

      ST_READ_ADDR: begin
        if (m_axi_arready) begin
          state_d = ST_READ_DATA;
        end
      end

      ST_READ_DATA: begin
        if (m_axi_rvalid) begin
          state_d = ST_IDLE;
        end
      end

      default: begin
        state_d = ST_IDLE;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q     <= ST_IDLE;
      req_write_q <= 1'b0;
      req_addr_q  <= '0;
      req_size_q  <= MEM_SIZE_4;
      req_wdata_q <= '0;
    end else begin
      state_q <= state_d;

      // Latch request on transition from IDLE
      if (state_q == ST_IDLE && wasm_req_i.valid) begin
        req_write_q <= wasm_req_i.write;
        req_addr_q  <= wasm_req_i.addr;
        req_size_q  <= wasm_req_i.size;
        req_wdata_q <= wasm_req_i.wdata;
      end
    end
  end

  //============================================================================
  // AXI Output Signals
  //============================================================================

  // Write address channel
  assign m_axi_awaddr  = BASE_ADDR + {req_addr_q[31:3], 3'b000};  // 64-bit aligned
  assign m_axi_awprot  = 3'b000;  // Unprivileged, secure, data access
  assign m_axi_awvalid = (state_q == ST_WRITE_ADDR);

  // Write data channel
  // Shift write data based on byte address offset within 64-bit word
  wire [2:0] wdata_shift = req_addr_q[2:0];
  assign m_axi_wdata  = req_wdata_q << (wdata_shift * 8);
  assign m_axi_wstrb  = gen_wstrb(req_size_q, wdata_shift);
  assign m_axi_wvalid = (state_q == ST_WRITE_DATA);

  // Write response channel
  assign m_axi_bready = (state_q == ST_WRITE_RESP);

  // Read address channel
  assign m_axi_araddr  = BASE_ADDR + {req_addr_q[31:3], 3'b000};  // 64-bit aligned
  assign m_axi_arprot  = 3'b000;
  assign m_axi_arvalid = (state_q == ST_READ_ADDR);

  // Read data channel
  assign m_axi_rready = (state_q == ST_READ_DATA);

  //============================================================================
  // WASM Response Signals
  //============================================================================

  // Ready: can accept new request when idle
  assign wasm_resp_o.ready = (state_q == ST_IDLE);

  // Read valid and data: shift received data to align with request address
  wire [2:0] rdata_shift = req_addr_q[2:0];
  assign wasm_resp_o.rvalid = (state_q == ST_READ_DATA) && m_axi_rvalid;
  assign wasm_resp_o.rdata  = m_axi_rdata >> (rdata_shift * 8);

  // Error: check AXI response codes (OKAY=00, SLVERR=10, DECERR=11)
  assign wasm_resp_o.error = ((state_q == ST_WRITE_RESP) && m_axi_bvalid && (m_axi_bresp != 2'b00)) ||
                              ((state_q == ST_READ_DATA) && m_axi_rvalid && (m_axi_rresp != 2'b00));

endmodule : wasm_axi_lite_adapter
