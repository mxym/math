#!/usr/bin/env python3
"""Second algorithm: a dual-number product recurrence, all exact integers.

This never forms any omitted-factor polynomial separately.  For each component
alpha it tracks the coefficient of a formal marker s in
prod_i (ell_i + s * conjugate(w_i) * v_i[alpha]).
"""

if not __debug__:
    raise SystemExit('Run without -O, -OO, or PYTHONOPTIMIZE: assertions are required for verification.')

import csv
import hashlib
import json
from math import factorial
from pathlib import Path

SOURCE = Path(__file__).resolve().parent
AUDIT = Path(__file__).resolve().parent
rows = [list(map(int, r)) for r in list(csv.reader((SOURCE/'witness_n200.csv').open()))[1:]]
gram_rows_digest = hashlib.sha256(json.dumps([r[:4] for r in rows], separators=(',', ':')).encode()).hexdigest()
assert gram_rows_digest == '3750bd80cb3284d579db0d32b0cdd2de101e6ee2766ec0e5e6983a26fec40462'

def plus(a, b):
    return (a[0]+b[0], a[1]+b[1])

def times(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])

def linear(p, a, b):
    out = [(0,0)]*(len(p)+1)
    for k, c in enumerate(p):
        out[k] = plus(out[k], times(a,c))
        out[k+1] = plus(out[k+1], times(b,c))
    return out

def norm(p):
    d = len(p)-1
    return sum(factorial(k)*factorial(d-k)*(u*u+v*v) for k,(u,v) in enumerate(p))

P = [(1,0)]
# Empty lists mean degree -1 zero. Four derivative polynomials:
# weighted coordinate 0, weighted coordinate 1, unweighted 0, unweighted 1.
D = [[],[],[],[]]
wnorm = 0
for ar, ai, br, bi, wr, wi in rows:
    a, b, cw = (ar,ai), (br,bi), (wr,-wi)
    weights = [times(cw,a), times(cw,b), a, b]
    for j, weight in enumerate(weights):
        next_d = linear(D[j],a,b) if D[j] else [(0,0)]*len(P)
        assert len(next_d) == len(P)
        D[j] = [plus(c,times(weight,p)) for c,p in zip(next_d,P)]
    P = linear(P,a,b)
    wnorm += wr*wr+wi*wi
permanent = norm(P)
num = norm(D[0])+norm(D[1])
den = permanent*wnorm
assert norm(D[2])+norm(D[3]) == len(rows)*permanent
assert 100*num > 269*den
assert 10*num < 27*den
old = json.loads((SOURCE/'EXACT_WITNESS_RESULT.json').read_text())
assert permanent == int(old['permanent'])
assert wnorm == int(old['w_norm_squared'])
assert num == int(old['w_star_Cw'])
assert den == int(old['permanent_times_w_norm_squared'])
result = {
    'PASS': True,
    'method': 'single-pass dual-number product derivative; no individual omitted products',
    'arithmetic': 'Python integer pairs',
    'n': len(rows),
    'input_sha256': hashlib.sha256((SOURCE/'witness_n200.csv').read_bytes()).hexdigest(),
    'frozen_gram_rows_hash_matches': True,
    'gram_rows_sha256': gram_rows_digest,
    'same_exact_permanent': True,
    'same_exact_rayleigh_numerator': True,
    'same_exact_vector_norm_squared': True,
    'all_ones_identity_verified': True,
    'lower_and_upper_rational_bounds_verified': True,
    'rayleigh_decimal_for_orientation_only': num/den,
}
(AUDIT/'n200_independent_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
