#!/usr/bin/env python3
"""Fail-closed audit of full Wakhare counterexample's Lean axiom roots."""
from pathlib import Path
import re
import sys

ROOTS = {
    'EntropyRoot.actual_polynomial_has_four_distinct_roots',
    'EntropyRoot.four_distinct_interior_roots',
    'EntropyRoot.eval_witnessPolynomial',
    'EntropyRoot.alpha_exists',
    'EntropyRoot.alpha_is_unique',
    'EntropyRoot.alpha_interval',
    'EntropyRoot.p1bound',
    'EntropyRoot.p2bound',
    'EntropyRoot.p3bound',
    'EntropyRoot.p4bound',
    'EntropyRoot.p5bound',
    'EntropyRoot.witness_parameters_admissible',
}
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def check(path: Path) -> None:
    log = path.read_text()
    pairs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    got = {}
    for name, raw in pairs:
        if name in got:
            raise ValueError(f'duplicate axiom report: {name}')
        got[name] = {x.strip() for x in raw.split(',') if x.strip()}
    if set(got) != ROOTS:
        raise ValueError(f'missing={sorted(ROOTS - set(got))}; extra={sorted(set(got)-ROOTS)}')
    for name, axioms in got.items():
        extra = axioms-STANDARD
        if extra:
            raise ValueError(f'nonstandard axiom at {name}: {sorted(extra)}')
    if 'sorryAx' in log or 'native_decide' in log:
        raise ValueError('untrusted axiom used')
    print(f'PASS: {len(got)} named Lean theorem roots, only standard kernel axioms')

if __name__=='__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: check_axioms.py audit-log.txt')
    check(Path(sys.argv[1]))
