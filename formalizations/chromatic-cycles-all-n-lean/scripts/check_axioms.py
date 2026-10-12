#!/usr/bin/env python3
"""Fail closed unless each exported root uses only standard Lean axioms."""
import re
import sys
from pathlib import Path

ROOTS = {
    "ChromaticCycleAll.cycleGraph_chromatic_polynomial_classification",
    "ChromaticCycleAll.every_actual_cycle_n_ge_17_fails",
    "ChromaticCycleAll.cycleGraph_colorings_all",
    "ChromaticCycleAll.coloring_card_eq_trace_all",
    "ChromaticCycleAll.cyclePolynomial_isChromatic",
    "ChromaticCycleAll.cycle12_negative",
    "ChromaticCycleAll.cycle13_negative",
    "ChromaticCycleAll.cycle14_negative",
    "ChromaticCycleAll.cycle15_negative",
    "ChromaticCycleAll.cycle16_negative",
    "ChromaticCycleAll.cycle11_infinitely_log_concave",
    "ChromaticCycleAll.cycle_binomial_infinite_classification",
    "ChromaticCycleAll.third_iterate_closed_formula",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def check(path: Path) -> None:
    log = path.read_text()
    pairs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, flags=re.S)
    reported = {}
    for theorem, block in pairs:
        if theorem in reported:
            raise ValueError(f"duplicate axiom inventory: {theorem}")
        reported[theorem] = {x.strip() for x in block.split(",") if x.strip()}
    if set(reported) != ROOTS:
        raise ValueError(f"missing={sorted(ROOTS-set(reported))}; extra={sorted(set(reported)-ROOTS)}")
    for theorem, axioms in reported.items():
        if axioms - STANDARD_AXIOMS:
            raise ValueError(f"unexpected axiom in {theorem}: {sorted(axioms-STANDARD_AXIOMS)}")
    if "sorryAx" in log or "native_decide" in log:
        raise ValueError("untrusted proof axiom found in log")
    print(f"PASS: {len(reported)} exported theorem roots checked; only propext, Classical.choice, Quot.sound")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: check_axioms.py <axiom-log>")
    check(Path(sys.argv[1]))
