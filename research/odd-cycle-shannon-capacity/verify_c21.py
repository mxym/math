#!/usr/bin/env python3
"""Audit the orbit, every floored-word pair, and every pair of inner vertices."""
from itertools import product, combinations
from math import comb

def check(ok, tag):
    if not ok: raise ValueError(tag)
def cd(x,m):
    x %= m
    return min(x,m-x)
def dist(x,y,m): return max(cd(a-b,m) for a,b in zip(x,y))

A=(1,5,26,130)
check(min(max(cd(a*k,682) for a in A) for k in range(1,682))==130,'orbit')
r0=list(range(1,130))
r1=[k for k in r0 if cd(5*k,682)<130]
check(r1==list(range(1,26))+list(range(111,130)),'first interval arithmetic')
r2=[k for k in r1 if cd(26*k,682)<130]
check(r2==[1,2,3,4,22,23,24,25,127,128,129],'second interval arithmetic')
check([cd(130*k,682) for k in r2]==[130,260,292,162,132,262,290,160,142,272,280],'last residues')
Z=[tuple((21*((t*a)%682))//682 for a in A) for t in range(682)]
check(len(set(Z))==682,'floor map collapsed two words')
md=min(dist(x,y,21) for x,y in combinations(Z,2))
check(md==4,'minimum quotient separation')
vertices=list(product(range(21),repeat=2))
lab=lambda p: (p[1]-2*p[0])%21
check(all(sum(lab(p)==z for p in vertices)==21 for z in range(21)),'fiber cardinality')
for p,q in combinations(vertices,2):
    if dist(p,q,21)<=1:
        check(1<=cd(lab(p)-lab(q),21)<=3,'invalid within-/cross-fiber separation')
N=682*21**4
check(N==132636042 and N>11466**2==131469156,'cardinality')
v=10359354480853559
check(v**8<N*10**120<(v+1)**8,'decimal bracket')
print('orbit size 682; circular separation 130; quotient pairs checked',comb(682,2))
print('floored separation',md,'; inner vertex pairs checked',comb(441,2))
print('C21 finite exponent 8:',N,'; 10.359354480853559 < N^(1/8) < 10.359354480853560')
