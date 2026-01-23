#!/usr/bin/env python3
"""
Run official WebAssembly test suite using the reference interpreter.
Parses .wast files, extracts modules and assertions, and runs tests.

Runs assertions in sequence against compiled modules, preserving state
between assertions (memory, globals, etc.) as required by the spec.
"""

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import List, Dict, Any, Tuple, Optional
from dataclasses import dataclass, field

# Paths
SCRIPT_DIR = Path(__file__).parent
PROJECT_DIR = SCRIPT_DIR.parent
WASM_INTERP = PROJECT_DIR / 'vendor' / 'spec' / 'interpreter' / 'wasm'
RUNNER_EXE = PROJECT_DIR / 'build' / 'Vwasm_runner'
WASM_DIR = PROJECT_DIR / 'build' / 'wasm_tests'


@dataclass
class TestCase:
    func_name: str
    args: List[Tuple[str, Any]]  # [(type, value), ...]
    expected: Optional[Tuple[str, Any]]  # (type, value) or None for trap
    is_trap: bool
    module_wat: str  # The WAT source for this test's module


@dataclass
class ModuleAssertion:
    """An assertion to be run against a compiled module."""
    func_name: str
    func_idx: int
    args: List[Tuple[str, Any]]
    expected: Optional[List[Tuple[str, Any]]]  # List of (type, value) for multi-value returns
    is_trap: bool
    is_invoke_only: bool = False  # Plain invoke for side effects
    alternatives: Optional[List[List[Tuple[str, Any]]]] = None  # For (either ...) - list of alternative expected results


@dataclass
class ModuleTestGroup:
    """A module with all its assertions."""
    module_wat: str
    assertions: List[ModuleAssertion] = field(default_factory=list)
    export_map: Dict[str, int] = field(default_factory=dict)


def convert_wat_to_wasm(wat_code: str, output_path: Path) -> bool:
    """Convert WAT text to WASM binary using the official interpreter."""
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


def parse_value(s: str) -> Tuple[str, Any]:
    """Parse a value like (i32.const 42) or (f32.const 1.5)."""
    # Handle integer types
    # -0x... is negative hex, 0x... is positive hex, -?[\d_]+ is decimal
    match = re.match(r'\(\s*(i32|i64)\.const\s+(-?0x[0-9a-fA-F_]+|-?[\d_]+)\s*\)', s)
    if match:
        vtype = match.group(1)
        val_str = match.group(2).replace('_', '')
        val = int(val_str, 16) if '0x' in val_str.lower() else int(val_str)
        return vtype, val

    # Handle float types (simplified - just handle common cases)
    match = re.match(r'\(\s*(f32|f64)\.const\s+([^\)]+)\)', s)
    if match:
        vtype = match.group(1)
        val_str = match.group(2).strip()
        # Handle special values
        if 'nan' in val_str.lower():
            is_negative = val_str.startswith('-')
            # Check for NaN with specific payload: nan:0x... or -nan:0x... (underscores allowed)
            nan_match = re.match(r'-?nan:0x([0-9a-fA-F_]+)', val_str)
            if nan_match:
                payload = int(nan_match.group(1).replace('_', ''), 16)
                return vtype, ('nan_payload', is_negative, payload)
            # Check for canonical NaN marker: nan:canonical
            if 'canonical' in val_str.lower():
                return vtype, ('nan_canonical', is_negative)
            # Check for arithmetic NaN: nan:arithmetic
            if 'arithmetic' in val_str.lower():
                return vtype, ('nan_arithmetic', is_negative)
            # Plain nan or -nan
            return vtype, ('nan_canonical', is_negative)
        if 'inf' in val_str.lower():
            return vtype, float('inf') if '-' not in val_str else float('-inf')
        try:
            val = float.fromhex(val_str) if 'x' in val_str.lower() else float(val_str)
            return vtype, val
        except:
            return None, None

    # Handle reference type null values: (ref.null func), (ref.null extern), (ref.null $t), (ref.null)
    match = re.match(r'\(\s*ref\.null(?:\s+(\w+|\$\w+))?\s*\)', s)
    if match:
        type_hint = match.group(1) if match.group(1) else 'func'
        # Determine the type based on hint
        if type_hint in ('extern', 'externref', 'noextern'):
            return 'externref', 0xFFFFFFFF  # REF_NULL_VALUE
        else:
            # func, funcref, nofunc, any, none, or user-defined types
            return 'funcref', 0xFFFFFFFF  # REF_NULL_VALUE

    # Handle external reference: (ref.extern N)
    match = re.match(r'\(\s*ref\.extern\s+(\d+)\s*\)', s)
    if match:
        val = int(match.group(1))
        return 'externref', val

    # Handle v128 types (SIMD vectors)
    # Format: (v128.const i8x16 v0 v1 ... v15) or similar lane types
    match = re.match(r'\(\s*v128\.const\s+(i8x16|i16x8|i32x4|i64x2|f32x4|f64x2)\s+(.+?)\s*\)', s)
    if match:
        lane_type = match.group(1)
        values_str = match.group(2)
        # Parse the individual lane values
        values = []
        for v in values_str.split():
            v = v.strip().replace('_', '')
            # Check for hex float first (0x...p or 0x...P with decimal point)
            # Handle +0x... as well as 0x... and -0x...
            if (v.startswith('0x') or v.startswith('-0x') or v.startswith('+0x')) and ('p' in v.lower() or '.' in v):
                # Hex float literal like 0x1.fffffep127
                try:
                    values.append(float.fromhex(v))
                except ValueError:
                    values.append(0.0)
            elif v.startswith('0x') or v.startswith('-0x') or v.startswith('+0x'):
                # Regular hex integer
                values.append(int(v, 16))
            elif '.' in v or 'e' in v.lower() or 'inf' in v.lower() or 'nan' in v.lower() or (lane_type.startswith('f') and v in ('-0', '+0')):
                # Float value
                if 'inf' in v.lower():
                    values.append(float('inf') if not v.startswith('-') else float('-inf'))
                elif 'nan' in v.lower():
                    # Handle -nan (negative NaN) vs nan (positive NaN)
                    # Check for NaN with specific payload: nan:0x... or -nan:0x... (underscores allowed)
                    import math
                    nan_match = re.match(r'-?nan:0x([0-9a-fA-F_]+)', v)
                    if nan_match:
                        payload = int(nan_match.group(1).replace('_', ''), 16)
                        # For f32: sign + 0x7F800000 (exponent) + payload
                        # For f64: sign + 0x7FF0000000000000 + payload
                        # We'll handle the bit manipulation during conversion
                        if v.startswith('-'):
                            values.append(('nan_payload', True, payload))
                        else:
                            values.append(('nan_payload', False, payload))
                    elif v.startswith('-'):
                        values.append(-float('nan'))  # Negative NaN
                    else:
                        values.append(float('nan'))   # Positive NaN
                else:
                    try:
                        values.append(float(v))
                    except ValueError:
                        values.append(0.0)
            else:
                values.append(int(v))

        # Convert to 128-bit value based on lane type
        import struct
        result = 0
        if lane_type == 'i8x16':
            for i, v in enumerate(values[:16]):
                result |= (v & 0xFF) << (i * 8)
        elif lane_type == 'i16x8':
            for i, v in enumerate(values[:8]):
                result |= (v & 0xFFFF) << (i * 16)
        elif lane_type == 'i32x4':
            for i, v in enumerate(values[:4]):
                result |= (v & 0xFFFFFFFF) << (i * 32)
        elif lane_type == 'i64x2':
            for i, v in enumerate(values[:2]):
                result |= (v & 0xFFFFFFFFFFFFFFFF) << (i * 64)
        elif lane_type == 'f32x4':
            for i, v in enumerate(values[:4]):
                if isinstance(v, tuple) and v[0] == 'nan_payload':
                    # Custom NaN with payload
                    is_negative, payload = v[1], v[2]
                    sign_bit = 0x80000000 if is_negative else 0
                    bits = sign_bit | 0x7F800000 | (payload & 0x7FFFFF)
                elif isinstance(v, (int, float)):
                    # For f32x4, interpret integers as float values (not raw bits)
                    bits = struct.unpack('<I', struct.pack('<f', float(v)))[0]
                else:
                    bits = v & 0xFFFFFFFF
                result |= bits << (i * 32)
        elif lane_type == 'f64x2':
            for i, v in enumerate(values[:2]):
                if isinstance(v, tuple) and v[0] == 'nan_payload':
                    # Custom NaN with payload
                    is_negative, payload = v[1], v[2]
                    sign_bit = 0x8000000000000000 if is_negative else 0
                    bits = sign_bit | 0x7FF0000000000000 | (payload & 0xFFFFFFFFFFFFF)
                elif isinstance(v, (int, float)):
                    # For f64x2, interpret integers as float values (not raw bits)
                    bits = struct.unpack('<Q', struct.pack('<d', float(v)))[0]
                else:
                    bits = v & 0xFFFFFFFFFFFFFFFF
                result |= bits << (i * 64)

        return 'v128', result

    return None, None


def parse_values(s: str) -> List[Tuple[str, Any]]:
    """Parse multiple values from a string."""
    values = []
    # Find individual value expressions (handle nested parens)
    i = 0
    while i < len(s):
        if s[i] == '(':
            end = find_matching_paren(s, i)
            if end != -1:
                expr = s[i:end+1]
                vtype, val = parse_value(expr)
                if vtype:
                    values.append((vtype, val))
                i = end + 1
            else:
                i += 1
        else:
            i += 1
    return values


def parse_either_alternatives(s: str) -> List[List[Tuple[str, Any]]]:
    """Parse (either ...) construct and return list of alternative result sets."""
    s = s.strip()
    if not s.startswith('(either'):
        return [parse_values(s)]  # Single result set

    # Find the content inside (either ...)
    if not s.startswith('(either'):
        return [parse_values(s)]

    # Extract alternatives from inside (either ...)
    inner = s[7:-1].strip()  # Remove "(either" and final ")"

    alternatives = []
    i = 0
    while i < len(inner):
        if inner[i] == '(':
            end = find_matching_paren(inner, i)
            if end != -1:
                alt_expr = inner[i:end+1]
                alt_values = parse_values(alt_expr)
                if alt_values:
                    alternatives.append(alt_values)
                i = end + 1
            else:
                i += 1
        else:
            i += 1

    return alternatives if alternatives else [parse_values(s)]


def find_matching_paren(text: str, start: int) -> int:
    """Find the index of the closing paren matching the open paren at start."""
    depth = 0
    i = start
    while i < len(text):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def extract_export_map(module: str) -> Dict[str, int]:
    """Extract the mapping of export names to function indices."""
    export_map = {}
    func_idx = 0

    # Find all function definitions (but not (func inside (type ...))
    pos = 0
    while pos < len(module):
        # Look for function definitions
        func_match = re.search(r'\(func\b', module[pos:])
        if not func_match:
            break

        start = pos + func_match.start()

        # Check if this (func is inside a (type ...) definition
        # by counting open parens before this position
        # A top-level func should have exactly 1 open paren (the module's)
        prefix = module[:start]
        paren_depth = prefix.count('(') - prefix.count(')')

        # Skip if nested too deep (inside a type definition)
        if paren_depth > 1:
            pos = start + 1
            continue

        end = find_matching_paren(module, start)
        if end == -1:
            break

        func_def = module[start:end+1]

        # Check for export in this function
        export_match = re.search(r'\(export\s+"([^"]+)"\)', func_def)
        if export_match:
            export_name = export_match.group(1)
            export_map[export_name] = func_idx

        func_idx += 1
        pos = end + 1

    return export_map


def extract_module_test_groups(content: str) -> List[ModuleTestGroup]:
    """Extract modules and their assertions from a .wast file."""
    groups = []
    current_group = None

    # Remove comments
    content = re.sub(r';;[^\n]*', '', content)
    content = re.sub(r'\(;.*?;\)', '', content, flags=re.DOTALL)

    pos = 0
    while pos < len(content):
        # Skip whitespace
        while pos < len(content) and content[pos].isspace():
            pos += 1
        if pos >= len(content):
            break

        if content[pos] != '(':
            pos += 1
            continue

        # Find the end of this S-expression
        end = find_matching_paren(content, pos)
        if end == -1:
            break

        expr = content[pos:end+1]

        # Check what kind of expression this is
        if expr.startswith('(module'):
            # Start a new module group
            if current_group and current_group.assertions:
                groups.append(current_group)
            # Skip modules that have imports - we don't support them
            if '(import ' in expr:
                current_group = None
                pos = end + 1
                continue
            current_group = ModuleTestGroup(
                module_wat=expr,
                export_map=extract_export_map(expr)
            )
        elif expr.startswith('(assert_return'):
            if current_group:
                assertion = parse_assertion(expr, current_group.export_map)
                if assertion:
                    current_group.assertions.append(assertion)
        elif expr.startswith('(assert_trap'):
            if current_group and '(invoke' in expr:
                assertion = parse_assertion(expr, current_group.export_map, is_trap=True)
                if assertion:
                    current_group.assertions.append(assertion)
        elif expr.startswith('(invoke'):
            # Plain invoke - run for side effects (void function)
            if current_group:
                assertion = parse_assertion(expr, current_group.export_map, is_invoke_only=True)
                if assertion:
                    current_group.assertions.append(assertion)

        pos = end + 1

    # Don't forget the last group
    if current_group and current_group.assertions:
        groups.append(current_group)

    return groups


def parse_assertion(expr: str, export_map: Dict[str, int], is_trap: bool = False, is_invoke_only: bool = False) -> Optional[ModuleAssertion]:
    """Parse an assertion expression."""
    # Find the invoke expression
    invoke_match = re.search(r'\(invoke\s+"([^"]+)"', expr)
    if not invoke_match:
        return None

    func_name = invoke_match.group(1)
    func_idx = export_map.get(func_name, -1)
    if func_idx < 0:
        return None

    # Find the end of the invoke expression
    invoke_start = invoke_match.start()
    invoke_end = find_matching_paren(expr, invoke_start)
    if invoke_end == -1:
        return None

    # Extract args from invoke
    args_start = invoke_match.end()
    args_str = expr[args_start:invoke_end]
    args = parse_values(args_str)

    # Extract expected values (supports multi-value returns and either alternatives)
    expected = None
    alternatives = None
    if not is_trap and not is_invoke_only:
        expected_str = expr[invoke_end+1:-1].strip()
        # Check for (either ...) construct
        if expected_str.startswith('(either'):
            alternatives = parse_either_alternatives(expected_str)
            # Use first alternative as primary expected for backwards compat
            expected = alternatives[0] if alternatives else None
        else:
            expected_values = parse_values(expected_str)
            expected = expected_values if expected_values else None

    return ModuleAssertion(
        func_name=func_name,
        func_idx=func_idx,
        args=args,
        expected=expected,
        is_trap=is_trap,
        is_invoke_only=is_invoke_only,
        alternatives=alternatives
    )


def encode_value(vtype: str, val):
    """Encode a value to (type_code, hex_value) or (type_code, lo64, hi64) for v128.
    type_code: 0=i32, 1=i64, 2=f32, 3=f64, 4=v128, 5=funcref, 6=externref
    Returns the raw bit representation."""
    import struct
    import math

    type_codes = {'i32': 0, 'i64': 1, 'f32': 2, 'f64': 3, 'v128': 4, 'funcref': 5, 'externref': 6}
    type_code = type_codes.get(vtype, 0)

    if vtype == 'v128':
        # Return type_code and lo/hi 64-bit parts
        lo64 = val & 0xFFFFFFFFFFFFFFFF
        hi64 = (val >> 64) & 0xFFFFFFFFFFFFFFFF
        return type_code, lo64, hi64

    if vtype in ('funcref', 'externref'):
        # Reference types are 32-bit values
        if isinstance(val, int):
            return type_code, val & 0xFFFFFFFF
        return type_code, 0xFFFFFFFF  # Default to null

    if vtype in ('i32', 'i64'):
        mask = 0xFFFFFFFF if vtype == 'i32' else 0xFFFFFFFFFFFFFFFF
        if isinstance(val, int):
            return type_code, val & mask
        return type_code, 0
    elif vtype == 'f32':
        if isinstance(val, tuple):
            nan_type = val[0]
            is_negative = val[1]
            sign_bit = 0x80000000 if is_negative else 0
            if nan_type == 'nan_payload':
                payload = val[2]
                return type_code, sign_bit | 0x7F800000 | (payload & 0x7FFFFF)
            return type_code, sign_bit | 0x7FC00000
        elif isinstance(val, float) and math.isnan(val):
            return type_code, 0x7FC00000
        else:
            return type_code, struct.unpack('<I', struct.pack('<f', val))[0]
    elif vtype == 'f64':
        if isinstance(val, tuple):
            nan_type = val[0]
            is_negative = val[1]
            sign_bit = 0x8000000000000000 if is_negative else 0
            if nan_type == 'nan_payload':
                payload = val[2]
                return type_code, sign_bit | 0x7FF0000000000000 | (payload & 0xFFFFFFFFFFFFF)
            return type_code, sign_bit | 0x7FF8000000000000
        elif isinstance(val, float) and math.isnan(val):
            return type_code, 0x7FF8000000000000
        else:
            return type_code, struct.unpack('<Q', struct.pack('<d', val))[0]
    return 0, 0


def get_functions_with_unsupported_opcodes(wasm_path: Path) -> set:
    """Check which functions in WASM binary transitively use unsupported opcodes (v3/GC features).
    Returns a set of function indices that directly or transitively use unsupported features."""
    try:
        with open(wasm_path, 'rb') as f:
            data = f.read()

        # Unsupported opcodes (v3/GC features we don't implement in hardware)
        unsupported_opcodes = {0x14, 0x15}  # call_ref, return_call_ref

        def read_leb128(pos):
            result = 0
            shift = 0
            while pos < len(data):
                byte = data[pos]
                pos += 1
                result |= (byte & 0x7f) << shift
                if (byte & 0x80) == 0:
                    break
                shift += 7
            return result, pos

        direct_unsupported = set()
        call_graph = {}

        # Find code section (section 10)
        pos = 8  # Skip magic + version
        while pos < len(data):
            section_id = data[pos]
            pos += 1
            size, pos = read_leb128(pos)

            if section_id == 10:  # Code section
                func_count, pos = read_leb128(pos)
                for func_idx in range(func_count):
                    body_size, pos = read_leb128(pos)
                    body_end = pos + body_size
                    call_graph[func_idx] = set()

                    # Skip locals declaration at start of function body
                    scan_pos = pos
                    local_count, scan_pos = read_leb128(scan_pos)
                    for _ in range(local_count):
                        _, scan_pos = read_leb128(scan_pos)  # count
                        scan_pos += 1  # type

                    # Scan this function's code for opcodes
                    while scan_pos < body_end:
                        opcode = data[scan_pos]
                        scan_pos += 1

                        if opcode in unsupported_opcodes:
                            direct_unsupported.add(func_idx)
                        elif opcode == 0x10:  # call instruction
                            callee, scan_pos = read_leb128(scan_pos)
                            call_graph[func_idx].add(callee)
                        # Skip immediates for common opcodes to avoid false positives
                        elif opcode in (0x02, 0x03, 0x04):  # block, loop, if
                            _, scan_pos = read_leb128(scan_pos)  # block type
                        elif opcode in (0x0C, 0x0D):  # br, br_if
                            _, scan_pos = read_leb128(scan_pos)  # label
                        elif opcode == 0x0E:  # br_table
                            vec_len, scan_pos = read_leb128(scan_pos)
                            for _ in range(vec_len + 1):  # +1 for default
                                _, scan_pos = read_leb128(scan_pos)
                        elif opcode == 0x11:  # call_indirect
                            _, scan_pos = read_leb128(scan_pos)  # type_idx
                            _, scan_pos = read_leb128(scan_pos)  # table_idx
                        elif opcode in (0x20, 0x21, 0x22, 0x23, 0x24):  # local/global ops
                            _, scan_pos = read_leb128(scan_pos)  # index
                        elif opcode in (0x25, 0x26):  # table.get, table.set
                            _, scan_pos = read_leb128(scan_pos)  # table_idx
                        elif 0x28 <= opcode <= 0x3E:  # memory load/store ops
                            _, scan_pos = read_leb128(scan_pos)  # align
                            _, scan_pos = read_leb128(scan_pos)  # offset
                        elif opcode in (0x3F, 0x40):  # memory.size, memory.grow
                            scan_pos += 1  # reserved byte
                        elif opcode == 0x41:  # i32.const
                            _, scan_pos = read_leb128(scan_pos)
                        elif opcode == 0x42:  # i64.const
                            _, scan_pos = read_leb128(scan_pos)
                        elif opcode == 0x43:  # f32.const
                            scan_pos += 4
                        elif opcode == 0x44:  # f64.const
                            scan_pos += 8
                        elif opcode == 0xD0:  # ref.null
                            _, scan_pos = read_leb128(scan_pos)  # heap type
                        elif opcode == 0xD2:  # ref.func
                            _, scan_pos = read_leb128(scan_pos)  # func_idx
                        elif opcode == 0xFC:  # misc prefix
                            sub_op, scan_pos = read_leb128(scan_pos)
                            # memory.fill, memory.copy, etc have mem_idx immediates
                            if sub_op in (0x0A, 0x0B):  # memory.copy, memory.fill
                                scan_pos += 1  # mem_idx (or two for copy)
                                if sub_op == 0x0A:
                                    scan_pos += 1
                            elif sub_op in (0x08, 0x09):  # memory.init, data.drop
                                _, scan_pos = read_leb128(scan_pos)  # data_idx
                                if sub_op == 0x08:
                                    scan_pos += 1  # mem_idx
                            elif sub_op in (0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11):  # table ops
                                _, scan_pos = read_leb128(scan_pos)  # elem/table idx
                                if sub_op in (0x0C, 0x0E):  # table.init, table.copy
                                    _, scan_pos = read_leb128(scan_pos)

                    pos = body_end

                # Compute transitive closure
                unsupported_funcs = set(direct_unsupported)
                changed = True
                while changed:
                    changed = False
                    for func_idx, callees in call_graph.items():
                        if func_idx not in unsupported_funcs:
                            if callees & unsupported_funcs:
                                unsupported_funcs.add(func_idx)
                                changed = True

                return unsupported_funcs
            else:
                pos += size

    except Exception:
        pass
    return set()


def run_module_tests(group: ModuleTestGroup, wasm_path: Path, verbose: bool = False) -> Tuple[int, int, int]:
    """Run all assertions for a module using the multi-test runner."""
    passed = 0
    failed = 0
    skipped = 0

    if not group.assertions:
        return 0, 0, 0

    # Check which functions use unsupported opcodes (v3/GC features)
    unsupported_funcs = get_functions_with_unsupported_opcodes(wasm_path)

    # Filter assertions to only include those with supported functions
    # Exception: tests expecting traps can still run (they'll trap anyway)
    supported_assertions = []
    for assertion in group.assertions:
        if assertion.func_idx in unsupported_funcs and not assertion.is_trap:
            skipped += 1
            if verbose:
                print(f"SKIP: {wasm_path.name} func {assertion.func_idx} (uses call_ref, v3/GC feature)")
        else:
            supported_assertions.append(assertion)

    if not supported_assertions:
        return 0, 0, skipped

    # Generate test list file
    # Format: <func_idx> <test_mode> <num_args> [<arg_type> <arg_hex>]... <num_results> [<result_type> <result_hex>]...
    # test_mode: 0=verify result, 1=expect trap, 2=run only (void function)
    # arg_type/result_type: 0=i32, 1=i64, 2=f32, 3=f64
    testlist_path = wasm_path.with_suffix('.tests')
    with open(testlist_path, 'w') as f:
        for assertion in supported_assertions:
            # Encode arguments
            args_str = ""
            for arg_type, arg_val in assertion.args:
                encoded = encode_value(arg_type, arg_val)
                if len(encoded) == 3:  # v128: (type_code, lo64, hi64)
                    type_code, lo64, hi64 = encoded
                    args_str += f" {type_code} {lo64:x} {hi64:x}"
                else:  # Regular: (type_code, value)
                    type_code, encoded_val = encoded
                    args_str += f" {type_code} {encoded_val:x}"

            num_args = len(assertion.args)

            if assertion.is_invoke_only or (assertion.expected is None and not assertion.is_trap):
                # Void function - run for side effects but don't verify result
                f.write(f"{assertion.func_idx} 2 {num_args}{args_str} 0\n")
                continue

            if assertion.is_trap:
                f.write(f"{assertion.func_idx} 1 {num_args}{args_str} 0\n")
            elif assertion.alternatives and len(assertion.alternatives) > 1:
                # Test with alternatives (mode 3) - any alternative can match
                # Format: <func> 3 <nargs> [args] <nalts> [<nresults> <results>]...
                alts_str = f" {len(assertion.alternatives)}"
                for alt in assertion.alternatives:
                    alt_results = ""
                    for exp_type, exp_val in alt:
                        encoded = encode_value(exp_type, exp_val)
                        if len(encoded) == 3:  # v128
                            type_code, lo64, hi64 = encoded
                            alt_results += f" {type_code} {lo64:x} {hi64:x}"
                        else:
                            type_code, encoded_val = encoded
                            alt_results += f" {type_code} {encoded_val:x}"
                    alts_str += f" {len(alt)}{alt_results}"
                f.write(f"{assertion.func_idx} 3 {num_args}{args_str}{alts_str}\n")
            else:
                # Encode all expected results (supports multi-value returns)
                results_str = ""
                for exp_type, exp_val in assertion.expected:
                    encoded = encode_value(exp_type, exp_val)
                    if len(encoded) == 3:  # v128
                        type_code, lo64, hi64 = encoded
                        results_str += f" {type_code} {lo64:x} {hi64:x}"
                    else:
                        type_code, encoded_val = encoded
                        results_str += f" {type_code} {encoded_val:x}"
                num_results = len(assertion.expected)
                f.write(f"{assertion.func_idx} 0 {num_args}{args_str} {num_results}{results_str}\n")

    # Count valid tests in the testlist
    with open(testlist_path) as f:
        valid_tests = len(f.readlines())

    if valid_tests == 0:
        return passed, failed, skipped

    # Run the multi-test runner
    try:
        result = subprocess.run(
            [str(RUNNER_EXE), f'+wasm={wasm_path}', f'+tests={testlist_path}'],
            capture_output=True, text=True, timeout=60
        )
        output = result.stdout + result.stderr

        # Parse results
        if 'PASS:' in output:
            # Extract count from "PASS: ... (N tests)"
            match = re.search(r'PASS:.*\((\d+) tests\)', output)
            if match:
                passed = int(match.group(1))
        elif 'FAIL:' in output:
            # Extract counts from "FAIL: ... (N passed, M failed)"
            match = re.search(r'FAIL:.*\((\d+) passed, (\d+) failed\)', output)
            if match:
                passed = int(match.group(1))
                failed = int(match.group(2))

            if verbose:
                # Show individual failures
                for line in output.split('\n'):
                    if line.startswith('FAIL:'):
                        print(line)

    except subprocess.TimeoutExpired:
        failed = valid_tests
        if verbose:
            print(f"TIMEOUT: {wasm_path}")

    return passed, failed, skipped


def extract_modules_and_tests(content: str) -> List[TestCase]:
    """Extract all test cases from a .wast file (legacy inline mode)."""
    tests = []
    current_module = None

    # Remove comments
    content = re.sub(r';;[^\n]*', '', content)
    content = re.sub(r'\(;.*?;\)', '', content, flags=re.DOTALL)

    pos = 0
    while pos < len(content):
        # Skip whitespace
        while pos < len(content) and content[pos].isspace():
            pos += 1
        if pos >= len(content):
            break

        if content[pos] != '(':
            pos += 1
            continue

        # Find the end of this S-expression
        end = find_matching_paren(content, pos)
        if end == -1:
            break

        expr = content[pos:end+1]

        # Check what kind of expression this is
        if expr.startswith('(module'):
            current_module = expr
        elif expr.startswith('(assert_return'):
            if current_module:
                test = parse_assert_return(expr, current_module)
                if test:
                    tests.append(test)
        elif expr.startswith('(assert_trap'):
            if current_module and '(invoke' in expr:
                test = parse_assert_trap(expr, current_module)
                if test:
                    tests.append(test)

        pos = end + 1

    return tests


def parse_assert_return(expr: str, module: str) -> Optional[TestCase]:
    """Parse an assert_return expression."""
    # Find the invoke expression
    invoke_match = re.search(r'\(invoke\s+"([^"]+)"', expr)
    if not invoke_match:
        return None

    func_name = invoke_match.group(1)

    # Find the end of the invoke expression
    invoke_start = invoke_match.start()
    invoke_end = find_matching_paren(expr, invoke_start)
    if invoke_end == -1:
        return None

    invoke_expr = expr[invoke_start:invoke_end+1]

    # Extract args from invoke (everything after the function name)
    args_start = invoke_match.end()
    args_str = expr[args_start:invoke_end]
    args = parse_values(args_str)

    # Extract expected value (everything after invoke, before final paren)
    expected_str = expr[invoke_end+1:-1].strip()
    expected_values = parse_values(expected_str)
    expected = expected_values[0] if expected_values else None

    # Create a test module that wraps the call
    test_module = create_test_module(module, func_name, args, expected)
    if not test_module:
        return None

    return TestCase(
        func_name=func_name,
        args=args,
        expected=expected,
        is_trap=False,
        module_wat=test_module
    )


def parse_assert_trap(expr: str, module: str) -> Optional[TestCase]:
    """Parse an assert_trap expression."""
    # Find the invoke expression
    invoke_match = re.search(r'\(invoke\s+"([^"]+)"', expr)
    if not invoke_match:
        return None

    func_name = invoke_match.group(1)

    # Find the end of the invoke expression
    invoke_start = invoke_match.start()
    invoke_end = find_matching_paren(expr, invoke_start)
    if invoke_end == -1:
        return None

    # Extract args from invoke
    args_start = invoke_match.end()
    args_str = expr[args_start:invoke_end]
    args = parse_values(args_str)

    # Determine result type from module's exported function
    result_type = get_func_result_type(module, func_name)

    test_module = create_test_module(module, func_name, args, None, result_type)
    if not test_module:
        return None

    return TestCase(
        func_name=func_name,
        args=args,
        expected=None,
        is_trap=True,
        module_wat=test_module
    )


def get_func_result_type(module: str, func_name: str) -> str:
    """Get the result type of an exported function."""
    # Look for (func (export "name") ... (result type) ...)
    pattern = rf'\(func[^)]*\(export\s+"{re.escape(func_name)}"\)[^)]*\(result\s+(\w+)\)'
    match = re.search(pattern, module)
    if match:
        return match.group(1)
    return 'i32'  # Default


def extract_memory_definition(module: str) -> Optional[str]:
    """Extract the memory definition from a module."""
    pos = 0
    while pos < len(module):
        match = re.search(r'\(memory\b', module[pos:])
        if not match:
            return None

        start = pos + match.start()
        prefix = module[:start]
        func_depth = prefix.count('(func') - prefix.count(')')
        if func_depth > 0:
            pos = start + 7
            continue

        end = find_matching_paren(module, start)
        if end == -1:
            return None

        mem_def = module[start:end+1]

        if 'memory.size' in mem_def or 'memory.grow' in mem_def:
            pos = start + 7
            continue

        return mem_def

    return None


def extract_data_segments(module: str) -> List[str]:
    """Extract standalone data segment definitions from a module."""
    segments = []
    pos = 0
    while pos < len(module):
        match = re.search(r'\(data\b', module[pos:])
        if not match:
            break

        start = pos + match.start()
        end = find_matching_paren(module, start)
        if end == -1:
            break

        data_def = module[start:end+1]

        is_inline = False
        depth = 0
        for i in range(start - 1, -1, -1):
            if module[i] == ')':
                depth += 1
            elif module[i] == '(':
                if depth > 0:
                    depth -= 1
                else:
                    if module[i:i+8] == '(memory ':
                        is_inline = True
                    break

        if not is_inline:
            if '(i32.const' in data_def or '(offset' in data_def:
                segments.append(data_def)

        pos = end + 1

    return segments


def create_test_module(module: str, func_name: str, args: List[Tuple[str, Any]],
                       expected: Optional[Tuple[str, Any]], result_type: str = None) -> Optional[str]:
    """Create a self-contained test module with inlined function body."""

    # Determine result type
    if expected:
        result_type = expected[0]
    elif not result_type:
        result_type = get_func_result_type(module, func_name)

    # Check if function has no result
    if result_type not in ('i32', 'i64', 'f32', 'f64'):
        return None

    # Extract the target function
    func_def = extract_function(module, func_name)
    if not func_def:
        return None

    # Check if function calls other functions - if so, we can't easily inline
    if '(call ' in func_def and '(call $' in func_def:
        return None

    # Extract the function body (everything after the signature)
    body_match = re.search(r'\(result\s+\w+\)\s*(.+)\)$', func_def, re.DOTALL)
    if not body_match:
        body_match = re.search(r'\(param[^)]+\)\s*(.+)\)$', func_def, re.DOTALL)
    if not body_match:
        return None

    body = body_match.group(1).strip()

    # Replace local.get with the actual argument values
    for i, (vtype, val) in enumerate(args):
        if vtype in ('i32', 'i64') and isinstance(val, int) and val < 0:
            mask = 0xFFFFFFFF if vtype == 'i32' else 0xFFFFFFFFFFFFFFFF
            val = val & mask
        # Handle NaN tuple markers
        if isinstance(val, tuple):
            nan_type = val[0]
            is_negative = val[1]
            sign = '-' if is_negative else ''
            if nan_type == 'nan_payload':
                payload = val[2]
                val_str = f'{sign}nan:0x{payload:x}'
            else:
                val_str = f'{sign}nan'
        else:
            val_str = str(val)
        body = re.sub(rf'\(local\.get\s+\$\w+\)', f'({vtype}.const {val_str})', body, count=1)
        body = re.sub(rf'\(local\.get\s+{i}\)', f'({vtype}.const {val_str})', body)

    # Check if function needs memory
    needs_memory = 'load' in body or 'store' in body or 'memory' in body

    # Build the test module
    test_module = '(module\n'
    if needs_memory:
        mem_def = extract_memory_definition(module)
        if mem_def:
            test_module += f'  {mem_def}\n'
        else:
            test_module += '  (memory 1)\n'

        data_segments = extract_data_segments(module)
        for seg in data_segments:
            test_module += f'  {seg}\n'

    test_module += f'  (func (export "test") (result {result_type})\n'
    test_module += f'    {body}\n'
    test_module += '  )\n'
    test_module += ')\n'

    return test_module


def extract_function(module: str, func_name: str) -> Optional[str]:
    """Extract a function definition from a module."""
    pattern = rf'\(func[^(]*\(export\s+"{re.escape(func_name)}"\)'
    match = re.search(pattern, module)
    if not match:
        return None

    start = match.start()
    end = find_matching_paren(module, start)
    if end == -1:
        return None

    return module[start:end+1]


def run_single_test(runner: Path, wasm_path: Path, expected: Any, is_trap: bool, is_i64: bool) -> Tuple[bool, str]:
    """Run a single test and return (passed, message)."""
    args = [str(runner), f'+wasm={wasm_path}']

    if is_trap:
        args.append('+trap')
    else:
        args.append(f'+expected={expected:x}')
        if is_i64:
            args.append('+i64')

    result = subprocess.run(args, capture_output=True, text=True, timeout=10)
    output = result.stdout + result.stderr

    passed = 'PASS' in output
    return passed, output.strip()


def run_tests_for_file(wast_path: Path, verbose: bool = False, use_full_module: bool = False) -> Tuple[int, int, int]:
    """Run all tests from a single .wast file. Returns (passed, failed, skipped)."""
    with open(wast_path) as f:
        content = f.read()

    if use_full_module:
        # Full-module mode: run assertions in sequence against compiled modules
        return run_tests_full_module_mode(wast_path, content, verbose)
    else:
        # Legacy inline mode
        return run_tests_inline_mode(wast_path, content, verbose)


def run_tests_full_module_mode(wast_path: Path, content: str, verbose: bool) -> Tuple[int, int, int]:
    """Run tests using full-module mode."""
    groups = extract_module_test_groups(content)

    total_passed = 0
    total_failed = 0
    total_skipped = 0

    for i, group in enumerate(groups):
        wasm_path = WASM_DIR / f'{wast_path.stem}_module_{i}.wasm'

        # Compile the full module
        if not wasm_path.exists():
            if not convert_wat_to_wasm(group.module_wat, wasm_path):
                total_skipped += len(group.assertions)
                if verbose:
                    print(f"SKIP: {wast_path.stem} module {i} (WAT conversion failed)")
                continue

        passed, failed, skipped = run_module_tests(group, wasm_path, verbose)
        total_passed += passed
        total_failed += failed
        total_skipped += skipped

    return total_passed, total_failed, total_skipped


def run_tests_inline_mode(wast_path: Path, content: str, verbose: bool) -> Tuple[int, int, int]:
    """Run tests using inline mode (original behavior)."""
    tests = extract_modules_and_tests(content)

    passed = 0
    failed = 0
    skipped = 0

    for i, test in enumerate(tests):
        wasm_path = WASM_DIR / f'{wast_path.stem}_{i}.wasm'

        # Convert to WASM (skip if already exists)
        if not wasm_path.exists():
            if not convert_wat_to_wasm(test.module_wat, wasm_path):
                skipped += 1
                if verbose:
                    print(f"SKIP: {wast_path.stem}:{test.func_name} (WAT conversion failed)")
                continue

        # Determine expected value
        if test.is_trap:
            expected = 0
            is_i64 = False
        elif test.expected is None:
            skipped += 1
            continue
        else:
            exp_type, exp_val = test.expected
            if exp_type in ('i32', 'i64'):
                mask = 0xFFFFFFFF if exp_type == 'i32' else 0xFFFFFFFFFFFFFFFF
                expected = exp_val & mask
                is_i64 = exp_type == 'i64'
            elif exp_type == 'f32':
                import struct
                import math
                if isinstance(exp_val, tuple):
                    nan_type = exp_val[0]
                    is_negative = exp_val[1]
                    sign_bit = 0x80000000 if is_negative else 0
                    if nan_type == 'nan_payload':
                        payload = exp_val[2]
                        expected = sign_bit | 0x7F800000 | (payload & 0x7FFFFF)
                    elif nan_type == 'nan_canonical':
                        expected = sign_bit | 0x7FC00000
                    elif nan_type == 'nan_arithmetic':
                        expected = sign_bit | 0x7FC00000
                    else:
                        expected = sign_bit | 0x7FC00000
                elif isinstance(exp_val, float) and math.isnan(exp_val):
                    expected = 0x7FC00000
                else:
                    expected = struct.unpack('<I', struct.pack('<f', exp_val))[0]
                is_i64 = False
            elif exp_type == 'f64':
                import struct
                import math
                if isinstance(exp_val, tuple):
                    nan_type = exp_val[0]
                    is_negative = exp_val[1]
                    sign_bit = 0x8000000000000000 if is_negative else 0
                    if nan_type == 'nan_payload':
                        payload = exp_val[2]
                        expected = sign_bit | 0x7FF0000000000000 | (payload & 0xFFFFFFFFFFFFF)
                    elif nan_type == 'nan_canonical':
                        expected = sign_bit | 0x7FF8000000000000
                    elif nan_type == 'nan_arithmetic':
                        expected = sign_bit | 0x7FF8000000000000
                    else:
                        expected = sign_bit | 0x7FF8000000000000
                elif isinstance(exp_val, float) and math.isnan(exp_val):
                    expected = 0x7FF8000000000000
                else:
                    expected = struct.unpack('<Q', struct.pack('<d', exp_val))[0]
                is_i64 = True
            else:
                skipped += 1
                continue

        # Run test
        try:
            test_passed, output = run_single_test(RUNNER_EXE, wasm_path, expected, test.is_trap, is_i64)
            if test_passed:
                passed += 1
            else:
                failed += 1
                if verbose:
                    print(f"FAIL: {wast_path.stem}:{test.func_name} {test.args} -> {output}")
        except subprocess.TimeoutExpired:
            failed += 1
            if verbose:
                print(f"TIMEOUT: {wast_path.stem}:{test.func_name}")
        except Exception as e:
            failed += 1
            if verbose:
                print(f"ERROR: {wast_path.stem}:{test.func_name} - {e}")

    return passed, failed, skipped


def main():
    if not WASM_INTERP.exists():
        print(f"Error: WebAssembly interpreter not found at {WASM_INTERP}")
        print("Build it with: cd vendor/spec/interpreter && make")
        sys.exit(1)

    if not RUNNER_EXE.exists():
        print(f"Error: Test runner not found at {RUNNER_EXE}")
        print("Build it with: make wasm-runner")
        sys.exit(1)

    WASM_DIR.mkdir(parents=True, exist_ok=True)

    verbose = '-v' in sys.argv or '--verbose' in sys.argv
    # Full-module mode is now the default (and only mode)
    use_full_module = True

    # Clean cached wasm files if requested
    if '--clean' in sys.argv:
        import shutil
        if WASM_DIR.exists():
            shutil.rmtree(WASM_DIR)
            WASM_DIR.mkdir(parents=True, exist_ok=True)
        print("Cleared cached WASM files")

    # Tests to skip - features not yet implemented
    SKIP_TESTS = {
        # WebAssembly 3.0 features (out of scope - defer to S-mode firmware)
        'multi-memory',   # v3 - defer to S-mode
        'memory64',       # v3 - defer to S-mode
        'gc',             # v3 - defer to S-mode
        'exception',      # v3 - defer to S-mode
        'call_ref',       # v3/GC - typed function references
        'return_call_ref',# v3/GC - tail call with typed refs
        'type-',          # v3/GC - type system tests
    }

    def should_skip_test(name: str) -> bool:
        """Check if a test should be skipped based on filename."""
        name_lower = name.lower()
        for skip in SKIP_TESTS:
            if skip in name_lower:
                return True
        return False

    # Determine which test files to run
    if '--all' in sys.argv:
        spec_dir = PROJECT_DIR / 'vendor' / 'spec' / 'test' / 'core'
        # Glob all .wast files and filter out unsupported tests
        all_wast = sorted(spec_dir.glob('*.wast'))
        # Also include bulk-memory tests
        bulk_memory_dir = spec_dir / 'bulk-memory'
        if bulk_memory_dir.exists():
            all_wast.extend(sorted(bulk_memory_dir.glob('*.wast')))
        # Also include SIMD tests
        simd_dir = spec_dir / 'simd'
        if simd_dir.exists():
            all_wast.extend(sorted(simd_dir.glob('*.wast')))
        # Also include relaxed-simd tests
        relaxed_simd_dir = spec_dir / 'relaxed-simd'
        if relaxed_simd_dir.exists():
            all_wast.extend(sorted(relaxed_simd_dir.glob('*.wast')))
        wast_files = [f for f in all_wast if not should_skip_test(f.name)]
    else:
        wast_files = [Path(arg) for arg in sys.argv[1:] if not arg.startswith('-')]
        if not wast_files:
            print("Usage: run_wasm_tests.py [--all] [--clean] [file.wast ...] [-v]")
            print("  --clean        Clear cached WASM files and regenerate")
            sys.exit(1)

    total_passed = 0
    total_failed = 0
    total_skipped = 0

    for wast_file in wast_files:
        if not wast_file.exists():
            print(f"Warning: {wast_file} not found")
            continue

        passed, failed, skipped = run_tests_for_file(wast_file, verbose, use_full_module)
        print(f"{wast_file.name}: {passed} passed, {failed} failed, {skipped} skipped")

        total_passed += passed
        total_failed += failed
        total_skipped += skipped

    print()
    print("=" * 60)
    print(f"Total: {total_passed + total_failed + total_skipped} tests")
    print(f"Passed: {total_passed}, Failed: {total_failed}, Skipped: {total_skipped}")
    print("=" * 60)

    if total_failed == 0:
        print("ALL TESTS PASSED!")

    sys.exit(0 if total_failed == 0 else 1)


if __name__ == '__main__':
    main()
