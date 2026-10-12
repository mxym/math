#!/usr/bin/env python3
"""Fail closed if any of the original 68 proof/pin bytes or signatures changed."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent.parent
for path,expected in json.loads((ROOT/'baseline/preserved-hashes.json').read_text()).items():
    if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=expected:
        raise RuntimeError('Protected baseline bytes changed: '+path)
for row in json.loads((ROOT/'source-integrity.json').read_text())['modules']:
    if hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()!=row['integrated_sha256']:
        raise RuntimeError('Exact imported source bytes changed: '+row['path'])
baseline=json.loads((ROOT/'baseline/coverage.json').read_text())
current=json.loads((ROOT/'coverage.json').read_text())
byname={row['name']:row for row in current}
if len(baseline)!=68 or len(current)!=101 or len(byname)!=101:
    raise RuntimeError('Unexpected original or current export count')
for row in baseline:
    if row['name'] not in byname:
        raise RuntimeError('Missing original theorem: '+row['name'])
    for field in ['exact_lean_signature','axioms','source']:
        if row[field]!=byname[row['name']][field]:
            raise RuntimeError('Original theorem '+field+' changed: '+row['name'])
print('PASS: every original 68 signature, axiom set, source path and protected proof/pin/reference/vendor byte is unchanged.')
