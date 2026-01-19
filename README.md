# wasm-cpu

A hardware WebAssembly processor implemented in SystemVerilog.

## Building

Requirements:
- Verilator
- Python 3
- OCaml and dune (for the reference interpreter)

Build the test runner:

```bash
make wasm-runner
```

Build the reference interpreter (needed for tests):

```bash
cd vendor/spec/interpreter && make
```

## Testing

Run the WebAssembly spec test suite:

```bash
make wasm-tests
```

## Features

Implemented:
- MVP integer operations (i32, i64)
- MVP floating-point operations (f32, f64)
- Linear memory
- Control flow (blocks, loops, branches, calls)
- Local and global variables

Not yet implemented:
- SIMD
- Reference types and tables
- Bulk memory operations
- Exception handling
- Threads and atomics
- Multiple memories
- Module linking and imports
