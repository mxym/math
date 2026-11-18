#!/usr/bin/env python3
"""Exact certificate for the degree-228 lower-prefix counterexample.
No third-party dependencies. Run with python3 verify.py, optionally under -O."""
from itertools import accumulate
from hashlib import sha256
from json import dumps

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def product(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out

def repeated(p, q, m):
    for _ in range(m):
        p = product(p, q)
    return p

# Route 1: multiply the five short factors.
f = repeated([1], [1, 1], 4)
f = repeated(f, [1, 0, -1, 0, 1], 5)
for d in [3, 4, 5]:
    f = repeated(f, [1] + [0] * (d-1) + [1], 17)

# Route 2: extract the q-integer ratio as a formal power series.
A = [2]*9 + [6]*12 + [8]*17 + [10]*17 + [12]*5
B = [1]*4 + [3]*17 + [4]*22 + [5]*17
require(len(A) == len(B) == 60, 'len(A) == len(B) == 60')
D = sum(A) - sum(B)
require(D == len(f)-1 == 228, 'D == len(f)-1 == 228')
g = [1] + [0]*D
for a in A:  # multiply by (1-q^a), no floating point or division
    for j in range(D, a-1, -1):
        g[j] -= g[j-a]
for b in B:  # divide by (1-q^b) in truncated formal series
    for j in range(b, D+1):
        g[j] += g[j-b]
require(f == g == f[::-1], 'f == g == f[::-1]')
require(min(f) == 1, 'min(f) == 1')
require(sum(f) == 2**55, 'sum(f) == 2**55')
require(sum(A[:9]) == 18 < 19 == sum(B[:9]), 'sum(A[:9]) == 18 < 19 == sum(B[:9])')
print(dumps({
    'degree': D, 'coefficient_count': len(f), 'minimum_coefficient': min(f),
    'negatives': sum(v<0 for v in f), 'zeroes': f.count(0),
    'first_eight': f[:8], 'middle': f[D//2], 'sum_coefficients': sum(f),
    'list_lengths': [len(A), len(B)], 'prefix_nine': [sum(A[:9]), sum(B[:9])],
    'failing_prefix_lengths': [i for i,(a,b) in enumerate(zip(accumulate(A),accumulate(B)),1) if a<b],
    'sha256_coefficients_csv_no_final_newline': sha256(','.join(map(str,f)).encode('ascii')).hexdigest(),
}, indent=2))
