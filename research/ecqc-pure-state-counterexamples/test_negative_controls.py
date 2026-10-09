#!/usr/bin/env python3
"""Reject deliberately invalid witnesses and corrupted certificates.

Runs entirely in memory; never edits the verifier source files.
Copyright (c) 2026 Yongxian Zhang. All rights reserved.
"""
from pathlib import Path
import importlib.util
import json
import subprocess
import sys

if not __debug__:
    raise RuntimeError('Assertions are required; do not run with python -O.')

HERE = Path(__file__).resolve().parent

def rejected(action, name):
    try:
        action()
    except (AssertionError, ValueError, ZeroDivisionError):
        return {'control': name, 'status': 'REJECTED_AS_REQUIRED'}
    raise RuntimeError(f'Invalid control unexpectedly passed: {name}')

def mutated_replay(old, new, filename='check_exact.py'):
    source = (HERE / filename).read_text(encoding='utf-8')
    assert source.count(old) == 1
    namespace = {'__name__': 'negative_control'}
    exec(compile(source.replace(old, new), '<deliberately-corrupted>', 'exec'), namespace)
    namespace['run']()

def run():
    spec = importlib.util.spec_from_file_location('interval_checker', HERE / 'check_intervals.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    results = []
    results.append(rejected(lambda: mutated_replay('rho[i][j] = F(1, 2)',
                                                    'rho[i][j] = F(1, 3)'),
                            'unnormalized Bell density'))
    results.append(rejected(lambda: mutated_replay('t = 2*(r-1)+j+k',
                                                    't = 2*(r-1)+j+k+1'),
                            'corrupted Born-law phase'))
    results.append(rejected(lambda: mutated_replay('F(3, 8), F(1, 16)]',
                                                    'F(3, 8), F(1, 8)]'),
                            'incorrect fifth cosine moment'))
    results.append(rejected(lambda: module.verify_diagonal_pure([1, 0, 0, 0, 0]),
                            'product state mislabeled as counterexample'))
    results.append(rejected(lambda: module.log_rational(module.Q(0)),
                            'logarithm outside positive domain'))
    results.append(rejected(lambda: mutated_replay(
        'W3=[[0,1,1],[-1,0,0],[-1,0,0]]',
        'W3=[[0,2,1],[-1,0,0],[-1,0,0]]', 'check_low_dimensions.py'),
        'corrupted qutrit quantum amplitude'))
    results.append(rejected(lambda: mutated_replay(
        'Pfull=[[0,25,25],[25,1,1],[25,1,1]]',
        'Pfull=[[0,24,25],[25,1,1],[25,1,1]]', 'check_low_dimensions.py'),
        'corrupted full-rank qutrit Born table'))
    results.append(rejected(lambda: mutated_replay(
        'denominator=3**243', 'denominator=3**244', 'check_low_dimensions.py'),
        'false integer logarithmic positivity certificate'))
    for filename in ['check_exact.py', 'check_intervals.py', 'check_low_dimensions.py']:
        proc = subprocess.run([sys.executable, '-O', str(HERE / filename)],
                              capture_output=True, text=True, timeout=30)
        if proc.returncode == 0 or 'Assertions are required' not in proc.stderr:
            raise RuntimeError(f'Optimized execution was not safely rejected: {filename}')
        results.append({'control': filename + ' under python -O',
                        'status': 'REJECTED_AS_REQUIRED'})
    return {'status': 'PASS', 'controls': results,
            'scope': 'These mutation tests detect selected faults, not arbitrary checker bugs.'}

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
