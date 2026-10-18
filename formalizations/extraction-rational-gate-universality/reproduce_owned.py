#!/usr/bin/env python3
"""Check this author source inventory; optionally run the guarded standard build.
This does not perform independent trust-zero replay or negative controls.
"""
import argparse, hashlib, json, pathlib, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parent
REPO=ROOT.parent.parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--check-only',action='store_true')
args=ap.parse_args()
inventory=json.loads((ROOT/'SOURCE_INVENTORY.json').read_text())
for path,expected in inventory['owned_inputs'].items():
    actual=hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
    if actual!=expected:raise RuntimeError('Author source drift: '+path)
print('AUTHOR_SOURCE_INVENTORY_PASS',len(inventory['owned_inputs']),flush=True)
if not args.check_only:
    command=['python3','/mnt/d/math/tmp/extraction-resume-20261018/worker_build.py',
        str(REPO),'formalizations/extraction-rational-gate-universality',
        'RationalGateUniversality','RationalGateUniversality.Check']
    sys.exit(subprocess.call(command))
