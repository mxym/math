#!/usr/bin/env python3
"""Exact toy CQ source: noncommuting 2x2 blocks and exhaustive two-universal seeds."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt

W=(F(0),)*3

# tuple=(upper left, real off-diagonal, lower right).
def add(*xs):
    return tuple(map(sum,zip(*xs))) if xs else W

def mul(c,x):
    return tuple(c*t for t in x)
def sub(x,y):
    return add(x,mul(-1,y))
def trace(x):
    return x[0]+x[2]
def hs(x,y):
    return x[0]*y[0]+2*x[1]*y[1]+x[2]*y[2]
def psd(x):
    return x[0]>=0 and x[2]>=0 and x[0]*x[2]>=x[1]**2

def noncomm(x,y):
    return ((x[0]-x[2])*y[1]-(y[0]-y[2])*x[1])!=0

def norm_upper(x,scale=10**12):
    r=(x[0]-x[2])**2+4*x[1]**2
    q=isqrt(r.numerator*scale**2//r.denominator)
    lo=F(q,scale)
    hi=lo if lo*lo==r else F(q+1,scale)
    assert lo*lo<=r<=hi*hi
    return max(abs(trace(x)),hi)

def hashblock(f,row):
    return tuple(add(*(x for i,x in enumerate(row) if f[i]==z)) for z in (0,1))

U=range(4)
a=(F(1,2),F(0),F(1,3),F(1,4))
b=(F(0),F(1,2),F(1,4),F(1,3))
rho={(x,y):mul(F(1,32),(1+(-1)**y*a[x],(-1)**y*b[x],1-(-1)**y*a[x]))
        for x,y in product(U,repeat=2)}
assert all(psd(v) for v in rho.values())
assert noncomm(rho[0,0],rho[1,0])
assert add(*rho.values())==(F(1,2),F(0),F(1,2))
marg1=tuple(add(*(rho[x,y] for y in U)) for x in U)
assert all(v==(F(1,8),F(0),F(1,8)) for v in marg1)
rows=tuple(tuple(rho[x,y] for y in U) for x in U)

# Each conditioning marginal in this example is s*I, so the sandwiched
# collision for a given classical prefix is sum Tr(R_x^2)/s.
def gamma(groups):
    ret=F(0)
    for group in groups:
        total=add(*group)
        assert total[1]==0 and total[0]==total[2]>0
        ret+=sum(hs(x,x)/total[0] for x in group)
    return ret

g1=gamma((marg1,));g2=gamma(rows)
chisums=[F(0),F(0)]
d2_mean_upper=F(0)
worst_bound=F(0)
for f in product((0,1),repeat=4):
    for i,R in enumerate(((marg1,),rows)):
        chisums[i]+=2*gamma(tuple(hashblock(f,r) for r in R))-1
    Z=defaultdict(list)
    for (x,y),z in rho.items(): Z[(f[x],f[y])].append(z)
    delta=[sub(add(*Z[z]),(F(1,8),F(0),F(1,8))) for z in product((0,1),repeat=2)]
    d_upper=sum(norm_upper(v) for v in delta)/2
    d2_mean_upper+=d_upper**2
    worst_bound=max(worst_bound,d_upper)
chis=tuple(r/16 for r in chisums)
assert chis==(g1,g2)
# log(1+x)>=2x/(2+x) for x>=0, so this is a rational lower bound
# on the theorem's log right-hand side, not a rounded evaluation.
theorem_lower=sum(x/(2+x) for x in chis)
assert d2_mean_upper/16<theorem_lower
print(f"noncommuting CQ: 16 seeds, side marginal I/2, conditional input collisions {g1},{g2}")
print(f"noncommuting CQ: exact expected hashed chi-square contrasts {chis[0]},{chis[1]}")
print(f"noncommuting CQ: certified E[D^2] < {theorem_lower} <= half-sum-log bound")
