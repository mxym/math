#!/usr/bin/env python3
"""Synthetic group-character and torus expansion checks; no search instances."""
from cmath import exp as cxexp
from itertools import product
from math import cos, exp, pi, sqrt
from random import Random
rng=Random(187)

def add(a,b,q): return tuple((x+y)%q for x,y in zip(a,b))
def scale(c,a,q): return tuple(c*x%q for x in a)
def dot(a,b,q): return sum(x*y for x,y in zip(a,b))%q
def rot(a,q): return (-a[-1]%q,)+a[:-1]
def orbit(a,q):
    out=set(); x=a
    for _ in a:
        out.add(x); out.add(scale(-1,x,q)); x=rot(x,q)
    return out
def mul(a,b,q):
    acc=(0,)*len(a); x=a
    for c in b:
        acc=add(acc,scale(c,x,q),q); x=rot(x,q)
    return acc
def bar(a,q): return (a[0],)+tuple(-x%q for x in a[:0:-1])

sectors=0
for q,d,k in ((3,2,1),(3,2,2),(5,2,1),(9,2,1),(3,4,1)):
    R=list(product(range(q),repeat=d))
    n=d*k
    for _ in range(70):
        A=[rng.choice(R) for i in range(k)]
        W=[rng.choice(R) for i in range(k)]
        e=rng.choice(R)
        u=(0,)*d
        for a,w in zip(A,W):
            u=add(u,mul(bar(a,q),w,q),q)
        assert all(sum(dot(w,mul(a,s,q),q) for a,w in zip(A,W))%q==dot(u,s,q) for s in R)
        phases=[(dot(e,s,q)-sum(dot(w,mul(a,s,q),q) for a,w in zip(A,W)))%q for s in R]
        if e==u:
            assert not any(phases)
        else:
            support={j:phases.count(j) for j in set(phases)}
            assert len(support)>1 and len(set(support.values()))==1
        sectors+=1

orbits=0
for q,d in ((3,4),(5,4),(9,4)):
    good=0
    for _ in range(110):
        A=[tuple(rng.randrange(q) for _ in range(d)) for t in range(2)]
        labels=list(product(range(q),repeat=2))
        U={h:add(scale(h[0],A[0],q),scale(h[1],A[1],q),q) for h in labels}
        if len(set(U.values()))<q*q:
            continue
        o={h:orbit(v,q) for h,v in U.items() if any(h)}
        if any(U[j] in row and j not in (h,scale(-1,h,q)) for h,row in o.items() for j in o):
            continue
        good+=1
        for h,v in U.items():
            if any(h):
                assert {j for j,vv in U.items() if vv in orbit(v,q)}=={h,scale(-1,h,q)}
                orbits+=1
    assert good>0

factor=0
for q in (3,5,9,15):
    for lam in (.003,.01,.04,.1):
        for j in range(32):
            z=j/32
            c=[sum(cxexp(1j*lam*cos(2*pi*(z-v/q)))*cxexp(-2j*pi*a*v/q)
                   for v in range(q))/q for a in range(q)]
            assert abs(c[0])<=1+1e-13
            for a in range(1,q):
                first=lam/2 if a in (1,q-1) else 0
                assert abs(c[a])<=first+lam*lam/2+1e-13
                factor+=1

collective=0
for q in (3,5,9):
    for m in (30,100,200):
        d=4000*m; b=1/d; a=.7; lam=a/sqrt(m); n=720
        z=[(x+.1)/n for x in range(n)]
        cs=[cxexp(1j*lam*cos(2*pi*x)) for x in z]
        # The two leading Fourier modes of each synthetic scalar law.
        u=sum(v*(1+2*b*cos(2*pi*x)) for v,x in zip(cs,z))/n
        g=sum(v*(1+2*b**(q*q)*cos(2*pi*q*x)) for v,x in zip(cs,z))/n
        ratio=(u**m-g**m).imag/(a*exp(-a*a/4)*b*sqrt(m))
        assert abs(ratio-1)<.02
        collective+=1

print("PASS exact sectors / signed orbit counts / scalar grid Fourier / collective scale:",
      sectors,orbits,factor,collective)
