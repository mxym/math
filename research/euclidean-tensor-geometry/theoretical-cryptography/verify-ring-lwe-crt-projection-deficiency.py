#!/usr/bin/env python3
"""Exact CRT and shared-phase identities, plus bounded numerical diagnostics."""
from itertools import product
from math import cos, log, pi, sqrt
from random import Random

def mul(a,b,q):
    d=len(a); c=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r=i+j; c[r%d]+=(-1 if r>=d else 1)*x*y
    return tuple(x%q for x in c)

def plus(a,b,q):
    return tuple((x+y)%q for x,y in zip(a,b))

def dot(a,b,q):
    return sum(x*y for x,y in zip(a,b))%q

def adj(a,q):
    return (a[0],)+tuple(-x%q for x in a[:0:-1])

def ideal(g,q):
    return {mul(g,u,q) for u in product(range(q),repeat=len(g))}

def ortho(S,q):
    return {w for w in product(range(q),repeat=len(next(iter(S)))) if all(dot(w,z,q)==0 for z in S)}

rng=Random(59)
lift_checks=phase_checks=first_second=tail_checks=0
for q,d0,g,h in ((3,4,(2,1,1,0),(2,2,1,0)),(5,2,(2,1),(3,1))):
    I0=ideal(g,q); J0=ideal(h,q)
    assert len(I0)*len(J0)==q**d0 and len(I0&J0)==1
    C0=ortho(I0,q)
    assert len(I0)*len(C0)==q**d0
    for u in range(d0):
        assert len({a[u] for a in J0})==q
    for a in C0:
        seq=[u if u<=q//2 else u-q for u in a]
        assert sum(x*x for x in seq)==0 or sum(x*x for x in seq)>=3
    for ell in (1,2,4,8):
        d=ell*d0
        G=tuple(g[i//ell] if i%ell==0 else 0 for i in range(d))
        H=tuple(h[i//ell] if i%ell==0 else 0 for i in range(d))
        for _ in range(12):
            s=tuple(rng.randrange(q) for _ in range(d))
            for base,lift,I in ((g,G,I0),(h,H,J0)):
                z=mul(lift,s,q)
                for j in range(ell):
                    strip=tuple(z[i] for i in range(j,d,ell))
                    v=tuple(s[i] for i in range(j,d,ell))
                    assert strip==mul(base,v,q) and strip in I
                    lift_checks+=1
    # Phase first and second moments hold for every fixed block position.
    for rep in range(160):
        Y=[rng.random() for _ in range(d0)]
        cosines=[[cos(2*pi*(y-a/q)) for y,a in zip(Y,z)] for z in I0]
        for i in range(d0):
            assert abs(sum(v[i] for v in cosines))<1e-12
            for j in range(d0):
                eig=sum(v[i]*v[j] for v in cosines)/len(cosines)
                assert abs(eig-(0.5 if i==j else 0))<1e-12
                first_second+=1
        for b in (1/64,1/128,1/256):
            W=[]
            for z in I0:
                vals=[]
                for y,a in zip(Y,z):
                    f=1+2*sum(b**(k*k)*cos(2*pi*k*(y-a/q)) for k in range(1,4))
                    G=1+2*b**(q*q)*cos(2*pi*q*y)
                    vals.append(f/G)
                w=1
                for v in vals:
                    w*=v
                W.append(w)
            for a in (0,.25,.5,1,2):
                phase=sum(w**(1+a) for w in W)/len(W)
                assert abs(phase-1-d0*a*(a+1)*b*b)<220*b**3
                phase_checks+=1

# Uniform ideal image under the shared-masking test, not a product of tests.
q=5; r=list(product(range(q),repeat=2)); zero=(0,0)
I=ideal((2,1),q); C=ortho(I,q)
images={w:ideal(w,q) for w in r}
image_checks=shared_nonproduct=0
for w1,w2 in product(r,repeat=2):
    K={plus(u,v,q) for u,v in product(images[w1],images[w2])}
    drawn1=[mul(adj(a,q),w1,q) for a in r]
    drawn2=[mul(adj(a,q),w2,q) for a in r]
    cnt=sum(plus(u,v,q) in C for u,v in product(drawn1,drawn2))
    assert cnt*len(K)==len(r)**2*len(K&C)
    shared_nonproduct+=sum(u not in C and v not in C and plus(u,v,q) in C
                           for u,v in product(drawn1,drawn2))
    image_checks+=1
assert shared_nonproduct>0

for chi in (0.5*log(3),0.5*log(5),0.75*log(7),0.2):
    for c in (1.07,1.25,1.7,2.4):
        for d in (2**24,2**27,2**29):
            t=chi-c*sqrt(2*chi*log(d)/d)
            D=d*(chi-t)-4*log(d)
            assert t>0 and D>0 and D*D/(4*t*d)>.5*log(d)
            tail_checks+=1
print("PASS block lifts / phase moments / tilted expansions / shared ideal images / moderate margins:",
      lift_checks,first_second,phase_checks,image_checks,tail_checks)
