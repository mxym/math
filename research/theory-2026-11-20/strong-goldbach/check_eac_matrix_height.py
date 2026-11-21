#!/usr/bin/env python3
"""Exact checks for the determinant and short-congruence examples."""
from fractions import Fraction as F
from math import lcm
from check_eac_historical_jets import eac, invert

def require(b, reason):
    if not b:
        raise RuntimeError(reason)

def determinant(rows):
    a = [list(map(F, r)) for r in rows]
    value = F(1)
    for j in range(len(a)):
        p = next((i for i in range(j, len(a)) if a[i][j]), None)
        if p is None:
            return F(0)
        if p != j:
            a[j], a[p] = a[p], a[j]
            value = -value
        q = a[j][j]
        value *= q
        for i in range(j + 1, len(a)):
            f = a[i][j]/q
            for t in range(j + 1, len(a)):
                a[i][t] -= f*a[j][t]
            a[i][j] = 0
    return value

def diff(a):
    return [[int(i == j)-x for j, x in enumerate(row)] for i, row in enumerate(a)]

a = [(0,0,1,2),(1,0,2,0),(0,2,0,2),(2,1,0,0)]
w = [sum(r) for r in invert(a)]
require(determinant(a)==14 and determinant(diff(a))==-5, "synthetic determinants")
require(w==[F(j,14) for j in (6,2,4,5)] and lcm(*(j.denominator for j in w))==14, "synthetic weights")
certs = [
    (128,(3,13,23),{3:2,7:1,5:-1,13:-1},(F(11,12),F(10,12)),(F(43,12),F(34,12))),
    (1718,(3,31,241),{3:1,211:1,5:-1,7:-1,31:-1},(F(6,7),F(6,7)),(F(112,42),F(292,42))),
    (1928,(3,5,641),{3:4,13:1,5:-3,7:-1},(F(8,9),F(8,9)),(F(288,9),F(62,9))),
]
for n, marks, want, heights, costs in certs:
    labels, a = eac(n)
    b = invert(a)
    ii, jj, kk = [labels.index(p) for p in marks]
    m = diff(a)
    u = [m[ii][i]-m[jj][i]-m[kk][i] for i in range(len(labels))]
    require({p:v for p,v in zip(labels,u) if v}==want, "short lattice witness")
    require(determinant(m)==0, "singular control")
    evaluate=lambda q:tuple(sum(max(0,u[i]*sign)*q[i] for i in range(len(labels))) for sign in (1,-1))
    require(evaluate([sum(r) for r in b])==heights, "heights")
    require(evaluate([sum(map(abs,r)) for r in b])==costs, "inverse-row costs")
    print(n,"PASS",heights,costs)
print("Synthetic det(A)=14, det(I-A)=-5, common denominator=14: PASS")
