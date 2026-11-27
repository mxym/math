#!/usr/bin/env python3
"""Exact checks of the tightness family, chain examples, and CI+MS coupling."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb

def tv(q,p):
    return sum(abs(q[x]-p[x]) for x in q)/2

def binomial_tv(N, t, k):
    # Independent one-dimensional exact formula, grouping by zero count.
    p=F(N+t,2*N)
    return sum(comb(k,j)*abs(p**j*(1-p)**(k-j)-F(1,2**k)) for j in range(k+1))/2

N=16;t=4;s=(N+t)//2
seeds=[frozenset(z) for z in combinations(range(N),s)]
assert len(seeds)==comb(16,10)==8008
for a,b in combinations(range(N),2):
    assert F(sum((a in z)==(b in z) for z in seeds),len(seeds))==F(1,2)
print("tightness finite seed family: N=16, 8008 functions, all 120 collision ratios 1/2")
checked=0
for t in range(4,43,2):
    N=t*t
    for k in sorted({1,min(2,N//16),min(7,N//16),N//16}):
        d=binomial_tv(N,t,k)
        assert d*d>=F(k,64*N)
        assert d*d<=F(k,2*N)
        checked+=1
print(f"tightness TV: {checked} exact binomial cases across even t=4..42")

def dist(bits,P,k):
    return {x:prod(P[xi] for xi in x) for x in product(bits,repeat=k)}

def prod(vals):
    p=F(1)
    for v in vals:p*=v
    return p

# Explicit classical conditional-i.i.d. case with distinguishable sector j.
ps=(F(1,3),F(2,3))
source=((F(7,8),F(1,8)),(F(3,5),F(2,5)))
d1=sum(p*tv(dict(enumerate(q)),{0:F(1,2),1:F(1,2)}) for p,q in zip(ps,source))
for k in range(1,8):
    pq={x:F(1,2**k) for x in product((0,1),repeat=k)}
    dk=sum(w*tv(dist((0,1),q,k),pq) for w,q in zip(ps,source))
    assert dk<=1-(1-d1)**k
    if k==3:print(f"conditional-i.i.d.: D_1={d1}, D_3={dk}, exact coupling bound={1-(1-d1)**3}")

# Marginal stationarity plus the raw-conditional entropy requirement does not imply CI.
p=(F(1,2),F(1,4),F(1,4))
Q=((F(1,2),F(1,2),F(0)),(F(1,2),F(0),F(1,2)),(F(1,2),F(0),F(1,2)))
assert tuple(sum(p[x]*Q[x][y] for x in range(3)) for y in range(3))==p
assert max(p)==sum(p[x]*max(Q[x]) for x in range(3))==F(1,2)
assert Q[0]!=p
print("strict comparison: stationary dependent Markov example has raw-conditional guessing probabilities 1/2,1/2 but not CI")

# Negative control: identical uniform raw blocks have equal stationary marginals,
# but not the same raw-conditional entropy. Use every balanced seed for N=16.
N=16
num=comb(N,N//2)
mu=F(2*comb(N-2,N//2-2),num)
assert mu==F(7,15)<F(1,2)
joint={(0,0):F(1,2),(0,1):F(0),(1,0):F(0),(1,1):F(1,2)}
d=tv(joint,dict.fromkeys(joint,F(1,4)))
assert d==F(1,2)
assert d*d>F(1,N)  # Even the relaxed linearized bound with the WRONG entropy would fail.
print("negative control: repeated raw block has D_2=1/2 despite uniform hashed marginals")
