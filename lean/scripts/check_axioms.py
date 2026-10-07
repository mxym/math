#!/usr/bin/env python3
"""Fail unless every literal #print axioms result is present and permitted."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent.parent
expected = json.loads((root / 'exported-theorems.json').read_text())
if len(expected)!=101 or len({row['name'] for row in expected})!=101:
    raise RuntimeError('Expected 101 distinct audited exports')
output = (root / 'logs/axioms.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
results = {}
for line in output.splitlines():
    if not line.strip():
        continue
    match = re.fullmatch(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", line)
    empty = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
    if not match and not empty:
        raise RuntimeError('Malformed or extraneous axiom output: ' + line)
    name = (match or empty).group(1)
    if name in results:
        raise RuntimeError(f'Duplicate axiom output for {name}')
    results[name] = [a.strip() for a in match.group(2).split(',') if a.strip()] if match else []
if set(results) != {item['name'] for item in expected}:
    raise RuntimeError('Missing or unexpected #print axioms result')
for item in expected:
    axioms = results[item['name']]
    if not set(axioms) <= allowed:
        raise RuntimeError(f"Unpermitted axiom for {item['name']}: {axioms}")
    item['axioms'] = axioms
(root / 'axiom-report.json').write_text(json.dumps(expected, indent=2) + '\n')
print(f'PASS: {len(expected)} exported theorems; axiom union = {sorted(set().union(*map(set, results.values())))}')
