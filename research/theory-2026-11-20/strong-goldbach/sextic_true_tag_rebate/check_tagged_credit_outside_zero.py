#!/usr/bin/env python3
"""Exact actual tag-cell restriction of the existing weighted intersection."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path

p = Path(__file__).resolve().with_name("check_tagged_negative_credit.py")
raw = p.read_bytes()
if sha256(raw).hexdigest() != "387e9434faa570bc14991c077b474f5ebb7d12ae686eeda0d762746a5e7a0fe1":
    raise ArithmeticError("different base checker")
source = raw.decode()
marker = "  cells.append((int(G*s),k,dh,m))"
if source.count(marker) != 1:
    raise ArithmeticError("ambiguous tag cell")
# The original half-open angle cell is (i/G,(i+1)/G].
# The quotient is .110-rough. Hence this is the exact .080 tag count.
source = source.replace(marker, '  cells.append((int(G*s),k,dh,m,int(u<=F(".080"))+int(v<=F(".080"))))')
setup, sep, _ = source.partition("\nAns=0\n")
if not sep:
    raise ArithmeticError("ambiguous replay boundary")
env = {"__file__": str(p)}
exec(compile(setup, str(p), "exec"), env)
cells,ambient,S,G = [env[k] for k in ("cells","ambient","S","G")]
if len(cells) != 961 or G != 500:
    raise ArithmeticError("old cells or grid changed")
ans = [[0]*3 for _ in range(3)]
for u,k,d,m,i in cells:
    for v,k2,d2,m2,j in cells:
        C = ambient(u+v)*S
        ans[i][j] += sum(max(0,k*m2[b]+k2*m[a]-C)*d[a]*d2[b] for a in range(3) for b in range(3))
tot=sum(map(sum,ans))
loss=F(".000176")
den=S**4*G**4
out=F(tot-ans[0][0],den)-loss
if not out > F(".156"):
    raise ArithmeticError("complete exterior credit failed")
print("ordered .080 tag count matrix, before common rank-nine debit:")
for row in ans:
    print([float(F(x,den)) for x in row])
print("suppress 00 only:",float(out))
print("suppress 00 and 11:",float(out-F(ans[1][1],den)))
print("suppress 00 and 22:",float(out-F(ans[2][2],den)))
print("suppress 00 and both 01 orientations:",float(out-F(ans[0][1]+ans[1][0],den)))
