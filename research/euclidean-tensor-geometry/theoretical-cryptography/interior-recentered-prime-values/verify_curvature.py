"""Finite, exact checks of the analytic alternative at constructed witnesses."""
from collections import defaultdict
from fractions import Fraction as Q
from math import prod, isqrt
from random import Random

rng=Random(73113)
cross=critical=mixed=overlap=0
for run in range(5500):
    R=rng.randrange(0,8)
    W=rng.randrange(0,7)
    M=R+W
    B=2*M
    D=20*(M+1)
    width=4*(B+1)
    a=rng.randrange(2,300)
    r=rng.randint(1,6)
    A=[a+rng.choice((-1,1))*(D+rng.randrange(1,60)) for _ in range(r)]
    if run%9==0: A[-1]=A[0] # allowed overlapping labels
    if min(A)<a<max(A): mixed+=1
    if len(set(A))<r: overlap+=1
    E=[0]*r
    S=[0]*r
    N=1
    for h in range(rng.randint(1,12)):
        j=rng.randrange(r)
        d=rng.randint(0,W) if h else 0
        e=rng.randint(1,4)
        for _ in range(rng.randrange(1,5)):
            z=rng.randint(-R,R)
            b=rng.randint(0,R)
            pairs=2 if z*z+b*b<=R*R and rng.randrange(2)==0 else 1
            offset=z-d
            D0=a-A[j]-offset
            N*=abs(D0 if pairs==1 else D0*D0+b*b)**e
            E[j]+=e*pairs
            S[j]+=e*pairs*offset
    mass=defaultdict(int)
    for A0,e,s in zip(A,E,S):
        assert abs(s)<=M*e
        if e: mass[Q(A0)+Q(s,e)]+=e
    assert 0<sum(E)<=N.bit_length()
    assert min(abs(a-c) for c in mass)>2*width

    def g(t):
        return abs(prod((t-c)**e for c,e in mass.items()))
    def der(t):
        return sum(Q(e)/(t-c) for c,e in mass.items())
    low,high=a-width,a+width
    if der(low)>=0>=der(high):
        critical+=1
    else:
        assert min(g(low),g(high)) <= N <= max(g(low),g(high))
        cross+=1

# Exact instance with no nearby level point for its true aggregate.
p,q=15877,15881
assert all(v%d for v in (p,q) for d in range(2,isqrt(v)+1))
assert (3+123)**2+1==p and (4-130)**2+5==q
assert p*q>126**4 and 126>100 and 127>100
assert (3+123)==-(3-129)==126
assert Q(2,3+123)+Q(2,3-129)==0
assert 2*126**2>36**2

print("PASS exact envelope alternatives: %d bracketed levels; %d critical brackets; %d mixed-side and %d overlapping-label inputs; stationary prime fixture." % (cross,critical,mixed,overlap))
