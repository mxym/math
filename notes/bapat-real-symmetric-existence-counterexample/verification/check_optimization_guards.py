#!/usr/bin/env python3
"""Negative tests: optimized assertion-based verification must fail closed.
This test deliberately uses explicit conditions, never Python assert statements.
"""
from pathlib import Path
import os
import subprocess
import sys

root = Path(__file__).resolve().parent
names = ['check_exact_algebra.py', 'check_independent_algebra.py',
         'check_integer_scaling.py', 'check_document_integrity.py']
cases = 0
for name in names:
    for label, flags, setting in [('-O', ['-O'], None), ('-OO', ['-OO'], None),
                                  ('PYTHONOPTIMIZE=1', [], '1'),
                                  ('PYTHONOPTIMIZE=2', [], '2')]:
        env = dict(os.environ)
        env.pop('PYTHONOPTIMIZE', None)
        if setting is not None:
            env['PYTHONOPTIMIZE'] = setting
        result = subprocess.run([sys.executable, *flags, str(root / name)],
                                env=env, text=True, capture_output=True)
        valid = (result.returncode == 2 and not result.stdout.strip()
                 and 'ERROR: assertions are disabled.' in result.stderr
                 and 'PASS' not in result.stdout and 'PASS' not in result.stderr)
        if not valid:
            raise SystemExit(f'FAIL: {name} under {label}: code={result.returncode}, '
                             f'stdout={result.stdout!r}, stderr={result.stderr!r}')
        print(f'PASS: {name} rejects {label} with exit 2 and no success output.')
        cases += 1
print(f'PASS: all {cases} fail-closed negative tests; no assertions used in this test driver.')
