#!/usr/bin/env python3
import re
import sys
import subprocess

if len(sys.argv) != 5:
    print(f"Usage: {sys.argv[0]} <srec_cat> <ldscript> <input.hex> <output.bin>")
    sys.exit(1)

srec_cat_path = sys.argv[1]
ldscript_path = sys.argv[2]
hex_path = sys.argv[3]
bin_path = sys.argv[4]

memory_block = False
min_addr = None
max_addr = None


def parse_length(value: str) -> int:
    value = value.strip()
    if value.endswith("K"):
        return int(value[:-1], 0) * 1024
    if value.endswith("M"):
        return int(value[:-1], 0) * 1024 * 1024
    return int(value, 0)


with open(ldscript_path, "r") as f:
    for line in f:
        line = line.strip()

        # Detect MEMORY block
        if line.startswith("MEMORY"):
            memory_block = True
            continue
        if memory_block and line.startswith("}"):
            memory_block = False
            continue
        if not memory_block:
            continue

        # Match memory entries
        m = re.match(
            r"(\w+)\s*\([^)]*\)\s*:\s*ORIGIN\s*=\s*([^,]+),\s*LENGTH\s*=\s*([^,}]+)",
            line,
        )
        if not m:
            continue

        name, origin_str, length_str = m.groups()

        if not name.endswith("_CODE"):
            continue

        origin = int(origin_str.strip(), 0)
        length = parse_length(length_str.strip())
        end = origin + length

        if min_addr is None or origin < min_addr:
            min_addr = origin

        if max_addr is None or end > max_addr:
            max_addr = end

if min_addr is None:
    print("Error: No *_CODE regions found", file=sys.stderr)
    sys.exit(2)

# Call srec_cat
cmd = [
    srec_cat_path,
    hex_path, "-Intel",
    "-crop", f"0x{min_addr:X}", f"0x{max_addr:X}",
    "-fill", "0xFF", f"0x{min_addr:X}", f"0x{max_addr:X}",
    "-offset", f"-0x{min_addr:X}",
    "-o", bin_path,
    "-Binary"
]

subprocess.check_call(cmd)
