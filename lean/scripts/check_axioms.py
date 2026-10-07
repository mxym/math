#!/usr/bin/env python3
"""Fail unless every literal #print axioms result is present and permitted."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent.parent
expected = json.loads((root / 'exported-theorems.json').read_text())
output = (root / 'logs/axioms.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
results = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
    if name in results:
        raise RuntimeError(f'Duplicate axiom output for {name}')
    results[name] = [a.strip() for a in axioms.split(',') if a.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
    if name in results:
        raise RuntimeError(f'Duplicate axiom output for {name}')
    results[name] = []
if set(results) != {item['name'] for item in expected}:
    raise RuntimeError('Missing or unexpected #print axioms result')
for item in expected:
    axioms = results[item['name']]
    if not set(axioms) <= allowed:
        raise RuntimeError(f"Unpermitted axiom for {item['name']}: {axioms}")
    item['axioms'] = axioms
(root / 'axiom-report.json').write_text(json.dumps(expected, indent=2) + '\n')
print(f'PASS: {len(expected)} exported theorems; axiom union = {sorted(set().union(*map(set, results.values())))}')
