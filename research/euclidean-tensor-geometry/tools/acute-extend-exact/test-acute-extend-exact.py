#!/usr/bin/env python3
"""Smoke-test the acute extension CLI using only the Python standard library."""
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys

COMMAND = [sys.executable, '-B', str(Path(__file__).with_name('acute-extend-exact.py'))]


def run(text, ok=True):
    result = subprocess.run(COMMAND, input=text, text=True, capture_output=True, check=False)
    if ok:
        assert result.returncode == 0, result.stderr
        return json.loads(result.stdout)
    assert result.returncode == 2 and result.stderr.startswith('acute-extend:'), result


def verify(A, x):
    points = [list(map(Fraction, p)) for p in A+[x]]
    assert len(set(map(tuple, points))) == len(points)
    for i, y in enumerate(points):
        for x, z in combinations(points[:i]+points[i+1:], 2):
            assert sum((a-b)*(c-b) for a,b,c in zip(x,y,z)) > 0


# Proper affine span; tests both exact decimal and quoted rational input.
r = run('[[0.125, "-1/3"], ["9/8", "-1/3"]]')
assert r == {'extendable': True, 'point': ['5/8', '2/3']}, r
verify([['1/8', '-1/3'], ['9/8', '-1/3']], r['point'])

# Full affine span; exercises the rational clipping success path.
points = [[4,8,-3],[3,1,7],[2,-8,-3],[-5,4,-6]]
r = run(json.dumps(points))
assert r['extendable'], r
verify(points, r['point'])
print('full-span extension:', r['point'])

# Full affine span and maximal; exercises the clipping failure path.
r = run('[[0,0],[2,0],[1,2]]')
assert r == {'extendable': False, 'maximum_squared_slack': '0', 'epigraph_vertices': 13}, r
print('maximal triangle:', r)

for bad in ['{', '[[0,0],[1,0],[2,0]]', '[[0,0],[0,0]]', '[[0,0],["1/0",0]]']:
    run(bad, ok=False)
print('PASS: 3 exact CLI cases, including decimal/rational parsing, and 4 invalid inputs.')
