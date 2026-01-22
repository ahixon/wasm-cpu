# wasm-cpu

A hardware WebAssembly processor implemented in SystemVerilog. Currently supports WebAssembly v1. v2 and v3 support are in progress.

[Discord](https://discord.gg/vJ52qVu3)

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
- Saturating truncation operations
- Linear memory (configurable, up to WASM32 maximum of 4 GB)
- Control flow (blocks, loops, branches, calls, call_indirect)
- Local and global variables
- Reference types (funcref, externref)
- Table operations (table.get, table.set, table.size, table.grow)
- Reference instructions (ref.null, ref.is_null, ref.func, ref.as_non_null)
- Reference branching (br_on_null, br_on_non_null)

Not yet implemented (skipped in tests):
- SIMD (128-bit vector operations)
- Bulk memory operations (memory.init, memory.copy, memory.fill)
- Element segment operations (table.init, elem.drop)
- Typed function references (call_ref, return_call_ref)
- Exception handling
- Multiple memories (multi-memory proposal)
- GC proposal
