# wasm-cpu

A hardware WebAssembly processor implemented in SystemVerilog. Currently supports WebAssembly v1. v2 and v3 support are in progress.

[Discord](https://discord.com/channels/1463596115394822196/1463596116565037232)

## Building

Requirements:
- Verilator (at least v5.038)
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

Not yet implemented (skipped in tests):
- SIMD (128-bit vector operations)
- Reference types (externref, funcref, typed function references)
- Bulk memory operations
- Exception handling
- Multiple memories (multi-memory proposal)
- GC proposal
