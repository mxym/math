#!/usr/bin/env python3
"""Mutation and optimized-mode controls for the universal 5/14 certificate.

The production proof checker uses explicit ArithmeticError checks; it
must fail closed if proof inputs, finite-enumeration coverage, or the strict
rational tail are corrupted. All temporary files are created and destroyed
in a temporary folder; the public source files are never modified.
"""
from pathlib import Path
import subprocess
import sys
import tempfile

SOURCE = Path(__file__).with_name("check_allrank_sharp_five_fourteenths_small.py")


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def run(src, python_options=()):
    with tempfile.TemporaryDirectory(prefix="johnson_5_14_") as path:
        copy = Path(path) / "check.py"
        copy.write_text(src, encoding="utf-8")
        return subprocess.run(
            [sys.executable, *python_options, str(copy)],
            capture_output=True, text=True,
            check=False,
        )


def main():
    original = SOURCE.read_text(encoding="utf-8")
    baseline = run(original)
    require(baseline.returncode == 0
            and "UNIVERSAL DUAL CERTIFICATE PASS" in baseline.stdout,
            "ordinary baseline replay failed")
    optimized = run(original, ("-O",))
    require(optimized.returncode == 0
            and "UNIVERSAL DUAL CERTIFICATE PASS" in optimized.stdout,
            "optimized Python silently suppressed explicit checks")
    tests = (
        ("modified rational input",
         "4_036_494", "4_036_495"),
        ("finite-tail gap", "MAX_MOVED = 43", "MAX_MOVED = 42"),
        ("tail exponent", "TAIL_HALF_EXPONENT = 22",
         "TAIL_HALF_EXPONENT = 21"),
        ("false strict tail", "Fraction(7, 50)",
         "Fraction(1, 10)"),
    )
    for label, old, new in tests:
        require(old in original, f"missing mutation anchor {label}")
        mutated = original.replace(old, new, 1)
        require(mutated != original, f"inert mutation {label}")
        result = run(mutated)
        require(result.returncode != 0
                and "ArithmeticError" in result.stderr,
                f"failed to reject mutation: {label}")
        print("EXPECTED REJECTION:", label, flush=True)
    print("ALL SMALL-DENOMINATOR NEGATIVE CONTROLS PASS; ORDINARY AND -O BOTH EXPLICITLY CHECKED")


if __name__ == "__main__":
    main()
