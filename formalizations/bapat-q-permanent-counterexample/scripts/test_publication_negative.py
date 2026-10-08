#!/usr/bin/env python3
"""Reject damaged public evidence with and without Python optimization.

No Lean is executed. Test copies live only under a temporary directory.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
REL = Path('formalizations/bapat-q-permanent-counterexample')
REPORT = Path('notes/bapat-q-permanent-counterexample/LEAN_VERIFICATION_2026-10-08.md')


def main():
    results = []
    for optimize in [False, True]:
        for mutation in ['corrupt_part', 'missing_retained_file', 'extra_public_file']:
            with tempfile.TemporaryDirectory(prefix='bapat-negative-') as temp:
                root = Path(temp) / 'repository'
                base = root / REL
                shutil.copytree(ROOT / REL, base)
                (root / REPORT).parent.mkdir(parents=True)
                shutil.copyfile(ROOT / REPORT, root / REPORT)
                if mutation == 'corrupt_part':
                    part = sorted((base / 'lossless-storage').iterdir())[0]
                    data = part.read_bytes()
                    part.write_bytes(bytes([data[0] ^ 1]) + data[1:])
                elif mutation == 'missing_retained_file':
                    (base / 'evidence/lean-toolchain').unlink()
                else:
                    (base / 'UNEXPECTED.txt').write_text('unexpected\n')
                command = [sys.executable] + (['-O'] if optimize else []) + [
                    '-B', str(base / 'scripts/check_publication.py')]
                result = subprocess.run(command, capture_output=True, text=True)
                if result.returncode == 0:
                    raise RuntimeError('Negative control accepted: ' + mutation)
                results.append({'mutation': mutation, 'optimized': optimize,
                                'rejected': True})
    print(json.dumps({'status': 'PASS', 'negative_controls': results,
                      'lean_executed': False}, indent=2))


if __name__ == '__main__':
    main()
