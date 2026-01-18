# WebAssembly CPU Makefile
# Supports Verilator, Icarus Verilog, and commercial simulators

# Default simulator
SIM ?= verilator

# Directories
RTL_DIR = rtl
TB_DIR = tb
SIM_DIR = sim
BUILD_DIR = build

# Source files
PKG_FILES = \
	$(RTL_DIR)/pkg/wasm_pkg.sv

RTL_FILES = \
	$(RTL_DIR)/core/wasm_stack.sv \
	$(RTL_DIR)/core/wasm_label_stack.sv \
	$(RTL_DIR)/core/wasm_call_stack.sv \
	$(RTL_DIR)/alu/wasm_alu_i32.sv \
	$(RTL_DIR)/alu/wasm_alu_i64.sv \
	$(RTL_DIR)/alu/wasm_fpu_f32.sv \
	$(RTL_DIR)/alu/wasm_fpu_f64.sv \
	$(RTL_DIR)/alu/wasm_conv.sv \
	$(RTL_DIR)/memory/wasm_memory.sv \
	$(RTL_DIR)/memory/wasm_locals.sv \
	$(RTL_DIR)/memory/wasm_globals.sv \
	$(RTL_DIR)/decoder/wasm_decoder.sv \
	$(RTL_DIR)/core/wasm_cpu.sv

TB_FILES = \
	$(TB_DIR)/wasm_cpu_tb.sv

ALL_FILES = $(PKG_FILES) $(RTL_FILES) $(TB_FILES)

# Verilator settings
VERILATOR = verilator
VERILATOR_FLAGS = --binary --timing -j 0 -Wall -Wno-fatal \
	--trace --trace-structs \
	-CFLAGS "-std=c++17" \
	--top-module wasm_cpu_tb

# Icarus Verilog settings
IVERILOG = iverilog
IVERILOG_FLAGS = -g2012 -Wall
VVP = vvp

# Output executable
VERILATOR_EXE = $(BUILD_DIR)/Vwasm_cpu_tb
IVERILOG_EXE = $(BUILD_DIR)/wasm_cpu_tb.vvp

.PHONY: all clean sim verilator iverilog lint help wasm-runner wasm-tests

all: sim

help:
	@echo "WebAssembly CPU Build System"
	@echo ""
	@echo "Targets:"
	@echo "  all        - Build and run simulation (default)"
	@echo "  sim        - Run simulation with selected simulator"
	@echo "  verilator  - Build and run with Verilator"
	@echo "  iverilog   - Build and run with Icarus Verilog"
	@echo "  wasm-tests - Run official WebAssembly test suite"
	@echo "  lint       - Run Verilator lint checks"
	@echo "  clean      - Remove build artifacts"
	@echo ""
	@echo "Variables:"
	@echo "  SIM=verilator|iverilog (default: verilator)"

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# Verilator build
$(VERILATOR_EXE): $(ALL_FILES) | $(BUILD_DIR)
	$(VERILATOR) $(VERILATOR_FLAGS) \
		--Mdir $(BUILD_DIR)/verilator_obj \
		-o $(abspath $(VERILATOR_EXE)) \
		$(ALL_FILES)

verilator: $(VERILATOR_EXE)
	./$(VERILATOR_EXE)

# Icarus Verilog build
$(IVERILOG_EXE): $(ALL_FILES) | $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(IVERILOG_EXE) $(ALL_FILES)

iverilog: $(IVERILOG_EXE)
	$(VVP) $(IVERILOG_EXE)

# Select simulator
ifeq ($(SIM),verilator)
sim: verilator
else ifeq ($(SIM),iverilog)
sim: iverilog
else
sim:
	@echo "Unknown simulator: $(SIM)"
	@echo "Supported: verilator, iverilog"
	@exit 1
endif

# Lint check
lint: | $(BUILD_DIR)
	$(VERILATOR) --lint-only -Wall $(ALL_FILES)

# Clean
clean:
	rm -rf $(BUILD_DIR)
	rm -f *.vcd *.fst

# Official WebAssembly test suite - plusargs-based runner
WASM_RUNNER_FILES = \
	$(RTL_DIR)/pkg/wasm_pkg.sv \
	$(RTL_FILES) \
	$(TB_DIR)/wasm_runner.sv

WASM_RUNNER_EXE = $(BUILD_DIR)/Vwasm_runner

$(WASM_RUNNER_EXE): $(WASM_RUNNER_FILES) | $(BUILD_DIR)
	$(VERILATOR) --binary --timing -j 0 -Wall -Wno-fatal \
		--top-module wasm_runner \
		--Mdir $(BUILD_DIR)/verilator_runner_obj \
		-o $(abspath $(WASM_RUNNER_EXE)) \
		$(WASM_RUNNER_FILES)

wasm-runner: $(WASM_RUNNER_EXE)

# Run official WebAssembly tests
wasm-tests: $(WASM_RUNNER_EXE)
	python3 scripts/run_wasm_tests.py --all

# File list for use by other tools
.PHONY: filelist
filelist:
	@echo $(ALL_FILES)
