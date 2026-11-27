#!/usr/bin/env python3
"""Exact Hermitian-rank test and independent 55-digit Born checks."""
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from itertools import combinations,product
from random import Random

# 1,z,...,z^5 in the basis (1,z) with z^2=z-1, z=exp(i*pi/3).
POW=((1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1))
PAIRS=((0,1),(0,2),(1,2))
EPS=F(1,100000)


def labels():
    # (missing coordinate, large coefficient site, small site, phase power)
    for j in range(3):
        yield 0,1,2,1+2*j
    for j in range(3):
        yield 1,2,0,2*j
    for j in range(3):
        yield 2,0,1,2*j


def effect(p,h):
    _,g,l,v=h
    diag=[F(0)]*3
    diag[g],diag[l]=p,1-p
    a,b=min(g,l),max(g,l)
    e=(v+3 if a==l else -v+3)%6
    # Off-diagonal coordinates divided by sqrt(p(1-p)) before elimination.
    off=[]
    for pair in PAIRS:
        off+=list(POW[e] if pair==(a,b) and 0<p<1 else (0,0))
    return diag+off,(a,b),e


def rank(A):
    A=[[F(x) for x in row] for row in A]
    r=0
    for j in range(len(A[0])):
        h=next((i for i in range(r,len(A)) if A[i][j]),None)
        if h is None:
            continue
        A[r],A[h]=A[h],A[r]
        for u in range(r+1,len(A)):
            f=A[u][j]/A[r][j]
            A[u]=[a-f*b for a,b in zip(A[u],A[r])]
        r+=1
        if r==len(A):
            break
    return r


def hs(p,A,B):
    a,P,e=A
    b,Q,f=B
    out=sum(x*y for x,y in zip(a[:3],b[:3]))
    if P==Q:
        m,n=POW[(e-f)%6]
        out+=2*p*(1-p)*(m+F(n,2))
    return out


def analyze():
    states=list(labels())
    for p in (F(1,2),F(1,2)+EPS,F(1,4),F(3,4),F(0),F(1)):
        E=[effect(p,h) for h in states]
        assert all(sum(e[0][:3])==1 for e in E)
        assert [sum(k[0][j] for k in E) for j in range(9)]==[3]*3+[0]*6
        assert rank([e[0] for e in E])==(9 if 0<p<1 else 3)
        for a,b in combinations(E,2):
            if p==F(1,2):
                assert hs(p,a,b)==F(1,4)
            elif a[1]!=b[1]:
                assert hs(p,a,b)==p*(1-p)
        if p==F(1,2)+EPS:
            assert any(hs(p,a,b)<F(1,4) for a,b in combinations(E,2))
    print("effects: exact normalization and tomography rank for 4 interior p, 2 rank-loss endpoints")
    print("effects: 36 SIC Gram pairs and perturbed non-SIC cross-group pairs PASS")


def inner_norm(p,psi):
    two=D(2)
    phases=[(D(a)+D(b)/two,D(b)*D(3).sqrt()/two) for a,b in POW]
    x,y=p.sqrt(),(1-p).sqrt()
    den=sum(a*a+b*b for a,b in psi)
    out=[]
    for _,g,l,e in labels():
        a,b=psi[g]
        c,d=psi[l]
        u,v=phases[e%6]
        # Absolute square of s*psi_g - a*conj(phase)*psi_l.
        z=x*a-y*(u*c+v*d)
        w=x*b-y*(u*d-v*c)
        out.append((z*z+w*w)/den)
    return out


def direct():
    rng=Random(260518291)
    count=[0,0,0]
    with localcontext() as ctx:
        ctx.prec=55
        p=D(50001)/D(100000)
        e=D(1)/D(100000)
        low=D('.5')+e/3
        for j in range(3):
            delta=[(D(int(k==j)),D(0)) for k in range(3)]
            assert abs(max(inner_norm(p,delta))-p)<D('1e-53')
        for k in range(3000):
            if k<1000:
                z=[(D(rng.randrange(-999,1000)),D(rng.randrange(-999,1000))) for _ in range(3)]
            else:
                i=k%3
                # Near both sides of sqrt(e), include small amplitude scales
                # and the far-region transition around 1/10.
                div=D(('0.000001','0.0002','0.002','0.0032','0.02','0.11')[k%6])
                z=[(D(rng.randrange(-1024,1025))/1024*div,
                    D(rng.randrange(-1024,1025))/1024*div) for _ in range(3)]
                z[i]=(D(1),D(0))
            Rp=inner_norm(p,z)
            R0=inner_norm(D('.5'),z)
            assert abs(sum(Rp)-3)<D('1e-51')
            assert abs(sum(R0)-3)<D('1e-51') and abs(sum(x*x for x in R0)-D('1.5'))<D('1e-51')
            assert max(Rp)>low-D('1e-51')
            den=sum(a*a+b*b for a,b in z)
            u2=min(1-(a*a+b*b)/den for a,b in z)
            count[0 if u2<=e else 1 if u2<=D('.01') else 2]+=1
        assert min(count)>0
    print(f"Born checks: 3000 deterministic 55-digit inputs, bins near-inner/near-outer/far {count}, plus coordinate states")


if __name__=='__main__':
    analyze()
    direct()
