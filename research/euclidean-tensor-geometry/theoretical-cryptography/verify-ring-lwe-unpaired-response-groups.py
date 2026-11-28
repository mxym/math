#!/usr/bin/env python3
"""Exact finite shuffle moments and checks for the Gaussian comparison constants."""
from fractions import Fraction as F
from itertools import permutations, product
from math import erf, exp, factorial, pi, prod, sqrt
from random import Random

def cycle_sizes(p):
    out=[];seen=set()
    for i in range(len(p)):
        if i in seen: continue
        j=i;n=0
        while j not in seen:
            seen.add(j);n+=1;j=p[j]
        out.append(n)
    return out

exact=orthogonal=0
for n in range(1,5):
    q=3
    ps=list(permutations(range(n)))
    # Integer numerator / 5; both marginals are uniform.
    M=lambda a,y: 7 if a==y else 4
    e2=eT=eorth=0
    for a in product(range(q),repeat=n):
        for y in product(range(q),repeat=n):
            H=sum(prod(M(a[i],y[p[i]]) for i in range(n)) for p in ps)
            T=sum(M(u,v)-5 for u in a for v in y)
            e2+=H*H
            eT+=T*T
            eorth+=(H-F(factorial(n)*5**n)-F(factorial(n)*5**(n-1),n)*T)*T
            exact+=1
    cycle=F(0)
    for p in ps:
        x=F(1)
        for m in cycle_sizes(p): x*=1+2*F(1,25)**m
        cycle+=x
    cycle/=len(ps)
    assert F(e2,q**(2*n)*(factorial(n)*5**n)**2)==cycle
    assert F(eT,q**(2*n)*(5*n)**2)==F(2,25)
    assert eorth==0
    assert cycle-1-F(2,25) <= F(2,25)**2/(1-F(2,25))
    orthogonal+=1

# A second cycle test: a 3x3 doubly stochastic paired measure with a nonsymmetric kernel.
A=((7,4,4),(5,8,2),(3,3,9))
B=tuple(tuple(sum(A[i][u]*A[j][u] for u in range(3)) for j in range(3)) for i in range(3))
def mul(a,b):
    return tuple(tuple(sum(a[i][j]*b[j][k] for j in range(3)) for k in range(3))
                 for i in range(3))
cur=((1,0,0),(0,1,0),(0,0,1))
tr=[None]
for k in range(1,5):
    cur=mul(cur,B)
    tr.append(F(sum(cur[i][i] for i in range(3)),225**k))
    assert tr[-1]>=1
for k in range(1,5):
    P=list(permutations(range(k)))
    c=F(0)
    for p in P:
        h=F(1)
        for j in cycle_sizes(p): h*=tr[j]
        c+=h
    c/=factorial(k)
    if k==1: assert c==tr[1]
    if k==2: assert c==(tr[1]**2+tr[2])/2

# Validate ideal character facts for the finite dyadic coefficient toy.
def ring(a,b,q):
    d=len(a)
    out=[0]*d
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            out[(i+j)%d]+=u*v*(-1 if i+j>=d else 1)
    return tuple(x%q for x in out)
coherence=0
from cmath import exp as cexp
for q,d in [(3,2),(3,4),(5,2),(9,2)]:
    S=list(product(range(q),repeat=d))
    roots=[cexp(2j*pi*a/q) for a in range(q)]
    for v in S[1:]:
        im=[ring(a,v,q) for a in S]
        for j in range(d):
            assert abs(sum(roots[a[j]] for a in im)) < 1e-10
            for k in range(j):
                assert abs(sum(roots[(a[j]+a[k])%q] for a in im))<1e-10
                assert abs(sum(roots[(a[j]-a[k])%q] for a in im))<1e-10
                coherence+=1

# Numerical probes for Gaussian comparison formulas and Taylor constants.
gauss=0
Phi=lambda x:(1+erf(x/sqrt(2)))/2
rng=Random(662)
Z=[(rng.gauss(0,1),rng.gauss(0,1)) for _ in range(140000)]
for m in (.03,.3,1.1,2.5):
    one=sum(abs(exp(sqrt(m)*x-m/2)-1) for x,y in Z)/(2*len(Z))
    two=sum(abs(exp(sqrt(m)*x-m/2)-exp(sqrt(m)*y-m/2)) for x,y in Z)/(2*len(Z))
    assert abs(one-(2*Phi(sqrt(m)/2)-1))<.015
    assert abs(two-(2*Phi(sqrt(m/2))-1))<.018
    gauss+=2
print("PASS shuffle leaves / first-order orthogonality / ideal Fourier moments / Gaussian tests:",
      exact,orthogonal,coherence,gauss)
