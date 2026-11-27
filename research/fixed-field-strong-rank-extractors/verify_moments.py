#!/usr/bin/env python3
"""Exact recurrence vs. polynomial moments; no randomness or dependencies."""
from fractions import Fraction as F
from functools import lru_cache
from math import prod

@lru_cache(None)
def g(q,d,s):
    if s==0: return 1
    if not 0<s<=d: return 0
    return g(q,d-1,s-1)+q**s*g(q,d-1,s)

def coef(q,s):
    return prod(1-q**j for j in range(1,s))

def signcoef(q,s):
    return (-1)**s*q**(s*(s-1)//2)

def polys(q,d,u):
    return (sum(coef(q,s)*g(q,d,s) for s in range(1,u+1)),
            sum(signcoef(q,s)*g(q,d,s) for s in range(u+1)))

def law(q,r):
    # Columns as independent uniform vectors in the ambient r-space.
    L={0:F(1)}
    for _ in range(r):
        N={}
        for j,p in L.items():
            stays=F(q**j,q**r)
            N[j]=N.get(j,0)+p*stays
            if j<r: N[j+1]=N.get(j+1,0)+p*(1-stays)
        L=N
    return {r-j:p for j,p in L.items()}

def uc(q,t):
    return (F(1,q**(t*(t-1)//2)*(q**t-1)),
            F(1,prod(q**j-1 for j in range(1,t+1))))

def run():
    qs=(2,3,4,5,7,8,9,16)
    tests=0
    for q in qs:
        for d in range(26):
            for u in range(17):
                P,H=polys(q,d,u)
                if u>=d: assert (P,H)==(d,int(d==0))
                elif u%2: assert P>=d and H<=int(d==0)
                else: assert P<=d and H>=int(d==0)
                tests+=1
    print(f'Newton exactness and both pointwise sandwich signs: {tests} (q,d,u) cases')
    nW=nPar=0
    for q in qs:
        for r in range(1,15):
            dist=law(q,r)
            assert sum(dist.values())==1
            mu=sum(d*p for d,p in dist.items()); full=dist[0]
            assert full==prod(1-F(1,q**j) for j in range(1,r+1))
            for s in range(r+1):
                val=sum(g(q,d,s)*p for d,p in dist.items())
                assert val==F(g(q,r,s),q**(r*s))
                nW+=1
            for delta in (F(1,2),F(1,10),F(1,1000),F(1,10**8),F(1,10**18)):
                t=1
                while max(uc(q,t))>delta/2:t+=2
                m=min(r,t); B=sum(abs(signcoef(q,s))*g(q,r,s) for s in range(1,m+1))
                eps=delta/(2*B)
                assert 1/eps <= 2*m*q**(r*m)/delta
                def ave(index,u):
                    return sum(p*polys(q,d,u)[index] for d,p in dist.items())
                for idx,ref in ((0,mu),(1,full)):
                    vals=[ave(idx,m)] if m==r else [ave(idx,m),ave(idx,m-1)]
                    assert min(vals)<=ref<=max(vals)
                    assert max(vals)-min(vals)<=delta/2
                nPar+=1
    print(f'Uniform-square laws from independent column process: {nW} exact moments')
    print(f'Cutoffs, two uniform sandwich widths, bias and size bounds: {nPar} parameter sets')
    for r in range(1,151):
        v=2**r
        nums=[g(2,r,s) for s in (1,2,3)]
        X,Y,Z=nums
        base=F(X,v)-F(Y,v**2)+F(3*Z,v**3)
        err=F(X+Y+3*Z,24*v**3)
        assert base==F(143,168)-F(5,8*v)-F(1,12*v*v)-F(1,7*v**3)
        assert 24*err==F(1,56)+F(1,24*v)+F(3,4*v*v)-F(17,21*v**3)
        assert base+err<F(1145,1344)<F(7,8)
    print('Binary finite-r baseline coefficient identities and strict 1145/1344 bound: r=1..150')
if __name__=='__main__': run()
