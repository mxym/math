#!/usr/bin/env python3
"""Finite algebra and geometric checks for the likelihood-field proof."""
from fractions import Fraction as F
from itertools import product
from math import log
from random import Random

rng=Random(111)
def rot(seq,j,p):
    d=len(seq); t=[0]*d
    for i,x in enumerate(seq):
        a,h=divmod(i+j,d)
        t[h]=(-1 if a%2 else 1)*x%p
    return tuple(t)
def adj(seq,p):
    return (seq[0],)+tuple(-x%p for x in seq[:0:-1])
def mul(x,y,p):
    d=len(x); z=[0]*d
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            h=i+j
            z[h%d]+=a*b*(-1 if h>=d else 1)
    return tuple(a%p for a in z)
def rank(A,p):
    A=[list(x) for x in A]; n=len(A); k=0
    for j in range(len(A[0])):
        i=next((i for i in range(k,n) if A[i][j]%p),None)
        if i is None: continue
        A[i],A[k]=A[k],A[i]
        inv=pow(A[k][j]%p,-1,p)
        A[k]=[x*inv%p for x in A[k]]
        for i in range(k+1,n):
            a=A[i][j]%p
            A[i]=[(u-a*v)%p for u,v in zip(A[i],A[k])]
        k+=1
    return k

ranks=0
for p in (2,3,5,7):
    for d in (2,4,8,16):
        E=[tuple(int(i==j) for i in range(d)) for j in range(d)]
        for h in range(1,d):
            for c in range(p):
                A=[tuple((v-c*w)%p for v,w in zip(u,rot(u,h,p))) for u in E]
                null=d-rank(A,p)
                if p==2 and c==1:
                    assert null==(h & -h)
                assert null<=d//2
                ranks+=1

adjoints=dual=0
for q in (2,3,4,5,6,9,15):
    G=list(product(range(q),repeat=2))
    for _ in range(100):
        a,b=rng.choice(G),rng.choice(G)
        for i in range(2):
            u=rot(adj(a,q),i,q)
            assert mul(a,b,q)[i]==sum(x*y for x,y in zip(u,b))%q
            adjoints+=1
        u,v=rng.choice(G),rng.choice(G)
        U={tuple(a*x%q for x in u) for a in range(q)}
        V={tuple(a*x%q for x in v) for a in range(q)}
        if len(U)==len(V)==q and len(U & V)==1:
            image={(sum(a*b for a,b in zip(u,s))%q,sum(a*b for a,b in zip(v,s))%q) for s in G}
            assert len(image)==q*q
            dual+=1

def bessels(t):
    a=t*t/4
    b0=1.; b1=t/2; s0=b0; s1=b1
    for j in range(1,155):
        b0*=a/(j*j); b1*=a/(j*(j+1))
        s0+=b0; s1+=b1
    return s0,s1
radial=0
for u in (0.1,0.25,0.5,1,2,4,6,9,12,15):
    i0,i1=bessels(u); r0=i1/i0; lam=u/(2*r0); D=1-r0*r0
    base=log(i0)-lam*(1+r0*r0)
    entropy=u*r0-log(i0)
    assert abs(lam*D+base+entropy)<1e-12
    for j in range(401):
        r=j/200
        a,b=bessels(2*lam*r)
        val=log(a)-lam*(1+r*r)
        assert val<=base+1e-12
        if abs(r-r0)>1e-7 and r>0:
            assert (b/a-r)*(r0-r)>0
        radial+=1

tables=0
for n in range(2,22):
    for _ in range(20):
        scores=[F(rng.randrange(-20,21),rng.randrange(1,11)) for i in range(n)]
        mean=sum(scores)/n; scores=[x-mean for x in scores]
        a=[[F(rng.randrange(-10,11),rng.randrange(1,11)) for j in range(n)] for i in range(n)]
        h=[sum(a[i][j]-a[j][i] for j in range(n))/(2*n) for i in range(n)]
        assert sum(h)==0
        t=sum((scores[i]-scores[j]-a[i][j])**2 for i,j in product(range(n),repeat=2))
        d=sum((h[i]-h[j]-a[i][j])**2 for i,j in product(range(n),repeat=2))
        assert t==d+2*n*sum((scores[i]-h[i])**2 for i in range(n))
        tables+=1

print("PASS kernel ranks, ring adjoints, separated dual pairs, circle radius, log-odds projection:",
      ranks,adjoints,dual,radial,tables)
