"""Finite exact checks of Vieta offsets, clearing, and merging."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import prod

checks=0
for A,E,S,t in ((A,E,S,t) for A,E,S,t in product(
        [(-3,9),(1,1),(0,2)], [(1,2),(4,4),(0,3),(8,6)], [(0,0),(2,-4),(-3,7)], range(-7,13))):
    D=prod(e**e for e in E if e)
    direct=prod((e*(t-a)-s)**e for a,e,s in zip(A,E,S) if e)
    mass=defaultdict(int)
    for a,e,s in zip(A,E,S):
        if e: mass[Q(a)+Q(s,e)]+=e
    assert D*prod((t-c)**e for c,e in mass.items())==direct
    centres=list(mass)
    H=sum(e*prod(t-d for d in centres if d!=c) for c,e in mass.items())
    if t not in mass:
        assert H == prod(t-c for c in centres)*sum(Q(e)/(t-c) for c,e in mass.items())
    else:
        assert H!=0
    checks+=1

# A quadratic with conjugate roots A+b +/- k*i has root sum 2(A+b).
# Translate by d, expand, and compare against the claimed signed offset.
translations=0
for A,b,k,d,e in product(range(-4,5),range(-3,4),range(4),range(6),range(1,5)):
    # F(X)=X^2+f1 X+f0; evaluating F(X+d).
    f1=-2*(A+b)
    f0=(A+b)**2+k*k
    new1=f1+2*d
    new0=f0+f1*d+d*d
    assert new1==-2*(A+b-d)
    assert new0==(A+b-d)**2+k*k
    assert e*(-new1-2*A)==2*e*(b-d)
    translations+=1

print("PASS aggregate algebra: %d denominator/derivative checks; %d exact signed Vieta translations." % (checks,translations))
