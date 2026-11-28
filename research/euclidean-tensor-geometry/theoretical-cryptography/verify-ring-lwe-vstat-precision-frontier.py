#!/usr/bin/env python3
"""Finite tolerance, likelihood, and ideal identities; abstract proof checks only."""
from fractions import Fraction as F
from itertools import product
from math import cos, log, pi, sqrt
from random import Random

tolcount=0
for n in (1,2,3,4,8,16,25,49,128,512,1728):
    for i,j in product(range(81),repeat=2):
        p0,p=F(i,80),F(j,80)
        ref=max(F(1,n*n),p0*(1-p0)/n)
        actual=max(F(1,n*n),p*(1-p)/n)
        if (p-p0)**2 <= ref/16:
            assert (p-p0)**2 <= actual
            tolcount+=1

rng=Random(53)
clipcount=0
for size in range(2,31):
    for _ in range(40):
        G=[F(1,size)]*size
        values=[rng.randrange(1,100) for _ in G]
        L=[F(v*size,sum(values)) for v in values]
        c=F(rng.randrange(1,130),80)
        Ustar=[min(c,y) for y in L]
        V=[x*F(rng.randrange(0,6),5) for x in L]
        for a,s,u in zip(L,Ustar,V):
            assert 0<=u<=a and u*u-s*s>=2*c*(u-s)
            clipcount+=1
        # Compare an allowed alternative of at least the retained mass.
        h=F(rng.randrange(0,6),5)
        U=[(1-h)*a+h*s for a,s in zip(L,Ustar)]
        assert sum(U)>=sum(Ustar) and sum(x*x for x in U)>=sum(x*x for x in Ustar)

def mul(a,b,q):
    d=len(a); c=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r=i+j
            c[r%d]+=(-1 if r>=d else 1)*x*y
    return tuple(x%q for x in c)

def sub(a,b,q):
    return tuple((x-y)%q for x,y in zip(a,b))

def dot(a,b,q):
    return sum(x*y for x,y in zip(a,b))%q

# Centering a positive trim by the conditional phase mean removes the
# constant label and constant response components exactly as in the paper.
# Ternary d=2 ring is a field; toy residual is deliberately nonproduct.
q=3; W=list(product(range(q),repeat=2))
G={(j,e):F(1,2*len(W)) for j,e in product(W,range(2))}
raw={(j,e):F(1+((j[0]*17+j[1]*5+e*7)%13),1) for (j,e) in G}
for e in range(2):
    mean=sum(raw[j,e] for j in W)/len(W)
    for j in W:
        raw[j,e]/=mean
phasechecks=0
for c in (F(2,3),F(1),F(6,5),F(5,3),F(3)):
    U={(j,e):min(c,raw[j,e]) for (j,e) in G}
    m=[sum(U[j,e] for j in W)/len(W) for e in range(2)]
    eta=1-sum(m)/2
    assert all(0<=x<=1 for x in m)
    Gamma={}
    for w in W:
        ans=F(0)
        for e in range(2):
            coeff=[sum((U[j,e] for j in W if dot(j,w,q)==i),F(0))/len(W) for i in range(3)]
            a,b=coeff[0]-coeff[2],coeff[1]-coeff[2]
            ans+=(a*a-a*b+b*b)/2
        Gamma[w]=ans
    assert sum(Gamma.values())==sum(G[j,e]*U[j,e]**2 for j,e in G)
    for h in (lambda s:F(1),lambda s:F(s[0]==0)-F(1,3),lambda s:F(s[1]==1)-F(1,3)):
        normh=sum(h(s)**2 for s in W)/len(W)
        lhs=F(0)
        for a in W:
            for (j,e),weight in G.items():
                v=sum(h(s)*(U[sub(j,mul(a,s,q),q),e]-m[e]) for s in W)/len(W)
                lhs+=v*v*weight/len(W)
                phasechecks+=1
        rhs=normh*sum(x for w,x in Gamma.items() if w!=(0,0))/len(W)
        assert lhs==rhs
    for a in W:
        for s in W:
            v=sum(G[j,e]*(raw[sub(j,mul(a,s,q),q),e]-U[sub(j,mul(a,s,q),q),e]) for j,e in G)
            assert v==eta

# Modular rank witnesses for the minimal ideal support staying bounded.
def rank(rows,p):
    m=[list(w) for w in rows]; r=0
    for j in range(len(m[0])):
        h=next((h for h in range(r,len(m)) if m[h][j]%p),None)
        if h is None:
            continue
        m[r],m[h]=m[h],m[r]
        a=pow(m[r][j],-1,p)
        m[r]=[a*x%p for x in m[r]]
        for h in range(r+1,len(m)):
            y=m[h][j]
            m[h]=[(u-y*v)%p for u,v in zip(m[h],m[r])]
        r+=1
    return r
idealcount=0
for p,d0,r0 in ((3,4,(2,1,1)),(5,2,(2,1))):
    for scale in (1,2,4,8,16):
        d=d0*scale
        r=tuple(r0[i//scale] if i%scale==0 and i//scale<len(r0) else 0 for i in range(d))
        rows=[mul(r,tuple(int(k==j) for k in range(d)),p) for j in range(d)]
        assert rank(rows,p)==d//2 and sum(a!=0 for a in r)==len(r0)
        idealcount+=1
for q in (9,15,45):
    p=3
    d=4
    div=q
    h=1
    while div%3==0:
        div//=3; h*=3
    r0=(2,1,1,0)
    def lift(a):
        return next(r for r in range(q) if r%h==(h//3)*a and r%div==0)
    r=tuple(lift(a) for a in r0)
    assert all(p*x%q==0 for x in r)
    vals={mul(r,a,q) for a in product(range(p),repeat=d)}
    assert len(vals)==9
    idealcount+=1

# Numerically stress the scalar cumulant coefficients at artificial widths.
# Nodes are equispaced; this is a diagnostic, not used by the proof.
mgfcount=0
for q in (3,5,9):
    for d in (32,64,128,256,512):
        for t in (0.37,1,2.25):
            b=0.7/d
            M=int(t/b**2)*d
            ff=[1+2*sum(b**(k*k)*cos(2*pi*k*j/256) for k in range(1,4)) for j in range(256)]
            gg=[1+2*b**(q*q)*cos(2*pi*q*j/256) for j in range(256)]
            for a in (-2,-0.25,0,0.3,0.8,1,1.125,2,2.4,4):
                ans=M*log(sum(f**a*g**(1-a) for f,g in zip(ff,gg))/256)
                target=t*a*(a-1)*d
                assert abs(ans-target)<(150/d)
                mgfcount+=1
saddlecount=0
for tt in range(1,17):
    t=tt/8
    for vv in range(80):
        v=vv/21
        x=t+2*sqrt(t*v)
        a=min(2,(x+t)/(2*t))
        optimum=(2-a)*x+t*a*(a-1)
        target=t+2*sqrt(t*v)-v if v<=t else 2*t
        assert abs(optimum-target)<1e-12
        for j in range(41):
            aa=j/20
            assert (2-aa)*x+t*aa*(aa-1)>=(optimum-1e-11)
        saddlecount+=1
print("PASS VSTAT tolerance / clipping / common phase / ideal witnesses / scalar mgf / saddle:",
      tolcount,clipcount,phasechecks,idealcount,mgfcount,saddlecount)
