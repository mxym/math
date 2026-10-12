#!/usr/bin/env python3
"""Read-only replay of the separately written finite/tail and constant checker."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parents[1] / 'notes' / 'mixed-bellman-product-join'
ENV = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}

def check(condition, message):
    if not condition:
        raise RuntimeError(message)

def main():
    for item in json.loads((ROOT / 'PROVENANCE.json').read_text())['files']:
        data = (ROOT / item['path']).read_bytes()
        check(len(data) == item['bytes'], 'Audit file size mismatch: ' + item['path'])
        check(hashlib.sha256(data).hexdigest() == item['sha256'], 'Audit file hash mismatch: ' + item['path'])
    original = json.loads((ROOT / 'independent_normal.json').read_text())
    for name, expected in original['certificate_sha256'].items():
        check(hashlib.sha256((SOURCE / name).read_bytes()).hexdigest() == expected, 'Certificate identity mismatch: ' + name)
    with tempfile.TemporaryDirectory(prefix='mixed-bellman-independent-') as directory:
        work = Path(directory)
        reports = []
        for mode in ('normal', 'optimized'):
            report = work / (mode + '.json')
            command = [sys.executable] + (['-O'] if mode == 'optimized' else []) + [str(ROOT / 'independent_replay.py'), str(SOURCE), '--report', str(report)]
            result = subprocess.run(command, cwd=work, env=ENV, text=True, capture_output=True)
            check(result.returncode == 0, 'Independent ' + mode + ' replay failed:\n' + result.stdout + result.stderr)
            print(result.stdout.rstrip(), flush=True)
            data = report.read_bytes()
            check(data == (ROOT / ('independent_' + mode + '.json')).read_bytes(), 'Saved ' + mode + ' evidence differs from fresh replay')
            reports.append(data)
        check(reports[0] == reports[1], 'Normal and optimized evidence differ')
    print('PASS: independent finite, tail and elementary-constant replay; exact original evidence reproduced in both modes.')
    print('Historical symbolic, corruption, interval-control and inherited-lower JSON records were hash-checked, not freshly rerun by this minimal runner.')

if __name__ == '__main__':
    main()
