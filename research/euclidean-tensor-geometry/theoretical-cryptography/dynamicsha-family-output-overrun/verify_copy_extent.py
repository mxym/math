#!/usr/bin/env python3
"""Check the Dynamic SHA / Dynamic SHA2 truncated-output copy-length defect."""

from __future__ import annotations

import re
import sys
from pathlib import Path

BLOCK_BITS = {224: 512, 256: 512, 384: 1024, 512: 1024}


def copied_bytes(hash_bits: int) -> int:
    return BLOCK_BITS[hash_bits] // 16


def expected_bytes(hash_bits: int) -> int:
    return (hash_bits + 7) // 8


def check_source(path: Path) -> None:
    text = path.read_text(encoding="utf-8", errors="strict")
    vulnerable = re.search(
        r"t\s*=\s*state->blocksize\s*/\s*16\s*;"
        r"\s*for\s*\(\s*i\s*=\s*0\s*;\s*i\s*<\s*t\s*;\s*i\+\+\s*\)"
        r"\s*hashval\s*\[\s*i\s*\]\s*=\s*hv\s*\[\s*i\s*\]\s*;",
        text,
    )
    fixed = re.search(
        r"t\s*=\s*\(\s*state->hashbitlen\s*\+\s*7\s*\)\s*/\s*8\s*;",
        text,
    )
    if vulnerable:
        status = "VULNERABLE COPY FORMULA PRESENT"
    elif fixed:
        status = "FIXED COPY FORMULA PRESENT"
    else:
        status = "EXPECTED COPY FORMULA NOT FOUND"
    print(f"{path}: {status}")


def main(argv: list[str]) -> int:
    print("bits expected copied overrun")
    observed = {}
    for bits in sorted(BLOCK_BITS):
        want = expected_bytes(bits)
        got = copied_bytes(bits)
        over = got - want
        observed[bits] = over
        print(f"{bits:4d} {want:8d} {got:6d} {over:7d}")

    assert observed == {224: 4, 256: 0, 384: 16, 512: 0}

    for arg in argv[1:]:
        check_source(Path(arg))

    print("PASS: shared formula overruns 224 by 4 bytes and 384 by 16 bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
