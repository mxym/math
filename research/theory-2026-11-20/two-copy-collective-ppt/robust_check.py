"""Checks exact bounds for the robustness note; run beside verify.py."""
from contextlib import redirect_stdout
from fractions import Fraction as Q
from io import StringIO
from pathlib import Path
from runpy import run_path
import sys

path = Path(__file__).with_name("verify.py")
args, sys.argv = sys.argv, [str(path)]
try:
    with redirect_stdout(StringIO()):
        proof = run_path(str(path))
finally:
    sys.argv = args

O, det, dag = (proof[x] for x in ("O", "det", "dag"))
coeff, sc, sub, sumv = (proof[x] for x in ("coeff", "sc", "sub", "sumv"))

def require(condition):
    if not condition:
        raise ValueError("exact certificate check failed")

minors = []
for tag, vs in sorted(proof["sectors"].items()):
    block = [[sumv(sc(x*y, coeff(a,c,b,d))
                   for (a,c),x in v.items() for (b,d),y in w.items())
              for w in vs] for v in vs]
    for i, v in enumerate(vs):
        block[i][i] = sub(block[i][i], (120 * sum(x*x for x in v.values()), 0))
    require(block == dag(block))
    ds = [det([r[:k] for r in block[:k]]) for k in range(1, len(vs)+1)]
    require(all(v == 0 and u > 0 for u,v in ds))
    minors.extend(u for u,_ in ds)
    print(tag, [u for u,_ in ds])
require(len(minors) == 45 and min(minors) == 88)

for j, row_bound, frob2, ceil_frob in ((1,26,944,31), (3,109,16132,128), (4,30,1100,34)):
    T = proof["ts"][j]
    require(all(im == 0 for row in T for _,im in row))
    require(max(sum(abs(re) for re,_ in row) for row in T) == row_bound)
    require(sum(re*re for row in T for re,_ in row) == frob2 < ceil_frob**2)
require(3*98**2 < 170**2)
eta = Q(1, 20_000_000)
require(4400**2 < 1/eta and Q(81,2)/4400 < Q(1,100))
require(Q(81,2)*eta < Q(1,100))
require(Q(81,2)*Q(901,100) < Q(96,5)**2)
require(Q(1,100)+2*Q(96,5) < 39)
bound = 3 * (39 * (170*(26+109)+196*30)
             + 9*170*(31+128) + 147*12*34)
require(bound == 4_282_848)
require(Q(bound,4400) < 974 < 1079 < 120*(9-81*eta))
print("45 shifted exact positive minors (minimum 88); all rational bounds verified.")
