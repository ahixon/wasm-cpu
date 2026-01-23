#!/usr/bin/env python3
"""
FLOPS Benchmark Runner for WebAssembly SoC

Runs floating-point benchmarks and calculates FLOPS (Floating Point Operations Per Second)
for both scalar and SIMD (vectorized) operations.

Usage:
    python3 run_flops_benchmark.py [--iterations N] [--clock-mhz MHZ]
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Tuple

# Paths
SCRIPT_DIR = Path(__file__).parent
PROJECT_DIR = SCRIPT_DIR.parent
WASM_INTERP = PROJECT_DIR / 'vendor' / 'spec' / 'interpreter' / 'wasm'
RUNNER_EXE = PROJECT_DIR / 'build' / 'Vwasm_runner'
BENCHMARK_WAST = PROJECT_DIR / 'benchmarks' / 'flops_benchmark.wast'


@dataclass
class BenchmarkResult:
    name: str
    iterations: int
    flops_per_iter: int
    total_flops: int
    wall_time_s: float
    mflops: float
    gflops: float


def convert_wat_to_wasm(wat_code: str, output_path: Path) -> bool:
    """Convert WAT text to WASM binary using the reference interpreter."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.wat', delete=False) as f:
        f.write(wat_code)
        wat_path = f.name

    try:
        result = subprocess.run(
            [str(WASM_INTERP), '-d', wat_path, '-o', str(output_path)],
            capture_output=True, text=True
        )
        return result.returncode == 0
    finally:
        os.unlink(wat_path)


def extract_module_from_wast(wast_path: Path) -> str:
    """Extract the module definition from the .wast file."""
    content = wast_path.read_text()
    # Find the module definition
    module_match = re.search(r'\(module\s[\s\S]*?\n\)', content)
    if module_match:
        return module_match.group(0)
    raise ValueError("No module found in .wast file")


def create_benchmark_wat(iterations: int) -> str:
    """Create a WAT module that runs all benchmarks and reports cycle counts.

    This module will be loaded and each benchmark function will be invoked
    with the specified number of iterations.
    """
    module_text = extract_module_from_wast(BENCHMARK_WAST)
    return module_text


def run_benchmark_function(
    wasm_path: Path,
    func_idx: int,
    iterations: int,
    result_type: str
) -> Tuple[float, Optional[str]]:
    """
    Run a benchmark function and return the wall-clock time.

    Returns:
        (wall_time_seconds, output) - wall time and the output string
    """
    # Create a test list file for this benchmark
    # Format: <func_idx> <test_mode> <num_args> [<arg_type> <arg_hex>]... <num_results> [<result_type> <result_hex>]...
    # test_mode: 2 = run only (void-like, we just want to run, not verify result)
    # arg_type: 0=i32
    # We'll use test_mode=2 to just run without verifying result

    arg_hex = format(iterations & 0xFFFFFFFF, 'x')

    # Create temp test list file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
        # func_idx, test_mode=2 (run only), num_args=1, arg_type=0 (i32), arg_value, num_results=0
        f.write(f"{func_idx} 2 1 0 {arg_hex} 0\n")
        testlist_path = f.name

    cmd = [str(RUNNER_EXE), f'+wasm={wasm_path}', f'+tests={testlist_path}']

    try:
        start_time = time.perf_counter()
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=600  # 10 minute timeout
        )
        end_time = time.perf_counter()

        wall_time = end_time - start_time
        output = result.stdout + result.stderr

        return wall_time, output

    except subprocess.TimeoutExpired:
        return -1, "TIMEOUT"
    except Exception as e:
        return -1, str(e)
    finally:
        os.unlink(testlist_path)


def calculate_flops(
    bench_name: str,
    iterations: int,
    wall_time_s: float
) -> BenchmarkResult:
    """Calculate FLOPS metrics for a benchmark run."""

    # FLOPs per iteration for each benchmark
    flops_map = {
        'bench_f32_scalar': 8,      # 4 mul + 4 add
        'bench_f64_scalar': 8,      # 4 mul + 4 add
        'bench_f32x4_simd': 32,     # 8 ops * 4 lanes
        'bench_f64x2_simd': 16,     # 8 ops * 2 lanes
        'bench_f32x4_intensive': 64, # 16 ops * 4 lanes
        'bench_f32x4_mixed': 16,    # 4 ops * 4 lanes
    }

    flops_per_iter = flops_map.get(bench_name, 8)
    total_flops = iterations * flops_per_iter

    # Calculate MFLOPS from wall time
    if wall_time_s > 0:
        mflops = (total_flops / wall_time_s) / 1_000_000
        gflops = mflops / 1000
    else:
        mflops = 0
        gflops = 0

    return BenchmarkResult(
        name=bench_name,
        iterations=iterations,
        flops_per_iter=flops_per_iter,
        total_flops=total_flops,
        wall_time_s=wall_time_s,
        mflops=mflops,
        gflops=gflops
    )


def print_results_table(results: list[BenchmarkResult]):
    """Print benchmark results in a formatted table."""
    print("\n" + "=" * 90)
    print("FLOPS BENCHMARK RESULTS (Verilator Simulation)")
    print("=" * 90)

    # Header
    print(f"{'Benchmark':<25} {'Iterations':>10} {'FLOPs':>12} {'Time (s)':>12} {'MFLOPS':>12} {'GFLOPS':>10}")
    print("-" * 90)

    # Results
    for r in results:
        print(f"{r.name:<25} {r.iterations:>10,} {r.total_flops:>12,} {r.wall_time_s:>12.3f} {r.mflops:>12.2f} {r.gflops:>10.4f}")

    print("-" * 90)

    # Summary
    scalar_results = [r for r in results if 'scalar' in r.name]
    simd_results = [r for r in results if 'simd' in r.name or 'intensive' in r.name]

    if scalar_results and simd_results:
        scalar_avg = sum(r.mflops for r in scalar_results) / len(scalar_results)
        simd_avg = sum(r.mflops for r in simd_results) / len(simd_results)
        speedup = simd_avg / scalar_avg if scalar_avg > 0 else 0

        print(f"\nScalar Average:     {scalar_avg:>12.4f} MFLOPS")
        print(f"SIMD Average:       {simd_avg:>12.4f} MFLOPS")
        print(f"SIMD Speedup:       {speedup:>12.2f}x")

    # Note about simulation
    print("\nNote: MFLOPS measured in Verilator simulation time, not real hardware.")
    print("      For hardware FLOPS, multiply by (sim_time / real_cycles) * clock_freq.")
    print("=" * 90)


def run_all_benchmarks(iterations: int, verbose: bool = False):
    """Run all FLOPS benchmarks and report results."""

    print(f"FLOPS Benchmark Suite")
    print(f"  Iterations: {iterations:,}")
    print()

    # Check dependencies
    if not WASM_INTERP.exists():
        print(f"ERROR: WASM interpreter not found at {WASM_INTERP}")
        print("  Run: make -C cpu/vendor/spec/interpreter")
        return 1

    if not RUNNER_EXE.exists():
        print(f"ERROR: WASM runner not found at {RUNNER_EXE}")
        print("  Run: make wasm-runner")
        return 1

    if not BENCHMARK_WAST.exists():
        print(f"ERROR: Benchmark file not found at {BENCHMARK_WAST}")
        return 1

    # Extract and compile the module
    print("Compiling benchmark module...")
    module_wat = extract_module_from_wast(BENCHMARK_WAST)

    wasm_path = PROJECT_DIR / 'build' / 'flops_benchmark.wasm'
    wasm_path.parent.mkdir(parents=True, exist_ok=True)

    if not convert_wat_to_wasm(module_wat, wasm_path):
        print("ERROR: Failed to compile benchmark module")
        return 1

    print(f"  Compiled to {wasm_path}")
    print()

    # Define benchmarks: (name, function_index, result_type)
    # Function indices based on export order in the module
    benchmarks = [
        ('bench_f32_scalar', 0, 'f32'),
        ('bench_f64_scalar', 1, 'f64'),
        ('bench_f32x4_simd', 2, 'v128'),
        ('bench_f64x2_simd', 3, 'v128'),
        ('bench_f32x4_intensive', 4, 'v128'),
        ('bench_f32x4_mixed', 5, 'v128'),
    ]

    results = []

    print("Running benchmarks...")
    for name, func_idx, result_type in benchmarks:
        print(f"  {name}...", end=' ', flush=True)

        wall_time, output = run_benchmark_function(wasm_path, func_idx, iterations, result_type)

        if wall_time < 0:
            print(f"FAILED: {output}")
            continue

        result = calculate_flops(name, iterations, wall_time)
        results.append(result)

        if verbose:
            print(f"OK ({wall_time:.3f}s, {result.mflops:.4f} MFLOPS)")
        else:
            print("OK")

    # Print results table
    print_results_table(results)

    return 0


def main():
    parser = argparse.ArgumentParser(
        description='Run FLOPS benchmarks on WebAssembly SoC'
    )
    parser.add_argument(
        '--iterations', '-n',
        type=int,
        default=1000,
        help='Number of iterations for each benchmark (default: 1000)'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Verbose output'
    )

    args = parser.parse_args()

    return run_all_benchmarks(args.iterations, args.verbose)


if __name__ == '__main__':
    sys.exit(main())
