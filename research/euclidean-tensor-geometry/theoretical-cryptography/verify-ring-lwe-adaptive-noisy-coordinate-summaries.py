#!/usr/bin/env python3
"""Exact shell algebra and synthetic Gaussian normalization for adaptive summaries."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import cos, erf, exp, pi, sin, sqrt
from random import Random

rng=Random(42)
def add(a,b,scale=1):
    c=Counter(a)
    for s,v in b.items():
        c[s]+=scale*v
    return {k:v for k,v in c.items() if v}
def mul(a,b):
    c=Counter()
    for s,u in a.items():
        for t,v in b.items():
            c[s^t]+=u*v
    return {k:v for k,v in c.items() if v}
def val(a,y):
    return sum(v*(-1 if (s&y).bit_count()%2 else 1) for s,v in a.items())

degree_checks=scalar_checks=0
for _ in range(72):
    n=5; size=1<<n; D=8
    polys=[{} for j in range(D+1)]
    exponents=[]
    for j,p in enumerate((1,2,3,1)):
        # At a fixed realized path the factor may use arbitrary numbers
        # determined by previous Gaussian transcript values.
        z=F(rng.randrange(-5,6),rng.randrange(1,6))
        prev_factor=F(1) if not exponents else F(1+max(0,z))
        candidates=[v for v in range(size) if v.bit_count()<=p]
        x={v:prev_factor*F(rng.randrange(-3,4),rng.randrange(1,5))
           for v in rng.sample(candidates,4)}
        exponents.append((p,z,x))
        polys[p]=add(polys[p],x,z)
        polys[2*p]=add(polys[2*p],mul(x,x),F(-1,2))
    C=[{0:F(1)}]
    for m in range(1,D+1):
        out={}
        for j in range(1,m+1):
            out=add(out,mul(polys[j],C[m-j]),F(j,m))
        assert all(s.bit_count()<=m for s in out)
        C.append(out)
        degree_checks+=len(out)
    for y in range(size):
        # Independent evaluation by multiplying the scalar one-step
        # exponentials (separately Taylor-expanded and then convolved).
        coeffs=[F(1)]+[F(0)]*D
        for p,z,x0 in exponents:
            x=val(x0,y); E=[F(0)]*(D+1)
            U=V=F(1)
            for a in range(D//p+1):
                if a: U*=z*x/a
                V=F(1)
                for b in range((D//p-a)//2+1):
                    if b: V*=(-x*x/2)/b
                    E[(a+2*b)*p]+=U*V
            coeffs=[sum(coeffs[a]*E[j-a] for a in range(j+1)) for j in range(D+1)]
        assert [val(c,y) for c in C]==coeffs
        scalar_checks+=1

def phi(x): return (1+erf(x/sqrt(2)))/2
# Exactly integrate the second Gaussian conditional on a half-line history
# in a simple two-query mathematical channel; phi is a numerical evaluation.
gauss=0
for x1 in (-.3,0.,.1):
    for xmin,xplus in ((.1,.42),(-.16,.2),(.0,-.3)):
        for u in (1.01,1.1,1.6):
            m=max(xmin*xmin,xplus*xplus)
            W=u*u*x1*x1+u**4*m
            for j in range(50):
                theta=2*pi*j/50
                a,c=u*cos(theta),u*sin(theta)
                b,d=u*u*cos(2*theta),u*u*sin(2*theta)
                # |G|^power leaves real drift power*a*x1 and
                # exponential residual (power²*a²-power*(a²-c²))/2.
                for power in (1,2):
                    r1=(power*(power-1)*a*a+power*c*c)/2
                    r2=(power*(power-1)*b*b+power*d*d)/2
                    val0=exp(r1*x1*x1)*(phi(-power*a*x1)*exp(r2*xmin*xmin)
                                         +phi(power*a*x1)*exp(r2*xplus*xplus))
                    assert val0<=exp(power*W/2)+1e-11
                    gauss+=1

features=0
for n in range(2,15):
    for _ in range(20):
        w=[rng.randrange(1,30) for j in range(n)]
        p=[F(a,sum(w)) for a in w]
        sumv=sum(sum(p[j]*abs(int(v==j)-p[v]) for j in range(n)) for v in range(n))
        assert sumv==2*sum(a*(1-a) for a in p)<=2
        features+=1

print("PASS coordinate-degree supports / scalar coefficients / Gaussian history / feature centering:",
      degree_checks,scalar_checks,gauss,features)
