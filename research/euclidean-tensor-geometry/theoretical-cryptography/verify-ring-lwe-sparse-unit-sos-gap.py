#!/usr/bin/env python3
"""Algebraic checks on artificial arrays; no decoding or optimization."""
from collections import Counter
from itertools import combinations, product
from math import gcd
from random import Random

def reduce_power(j,d):
    return j%d, (-1 if (j//d)%2 else 1)

def shift_vector(xs,t,q):
    d=len(xs); out=[0]*d
    for i,x in enumerate(xs):
        j,sign=reduce_power(i+t,d)
        out[j]=sign*x%q
    return out

def mul(a,s,q):
    d=len(s); m=[0]*d
    for i,x in a.items():
        for j,y in enumerate(s):
            t,sign=reduce_power(i+j,d)
            m[t]+=sign*x*y
    return [x%q for x in m]

def support_poly(I,d,u):
    return {reduce_power(-i,d)[0]:u*reduce_power(-i,d)[1] for i in I}

def shift_poly(a,t,d,q):
    out={}
    for i,x in a.items():
        j,sign=reduce_power(i+t,d)
        out[j]=(sign*x)%q
    return out

def poly_mod(a,b,q):
    a=a[:]
    while len(a)>=len(b):
        c=a[-1]*pow(b[-1],-1,q)%q
        s=len(a)-len(b)
        for i,v in enumerate(b):
            a[s+i]=(a[s+i]-c*v)%q
        while a and a[-1]==0:
            a.pop()
    return a

def poly_gcd(a,b,q):
    while b:
        a,b=b,poly_mod(a,b,q)
    return a

rng=Random(991)
units=0
for q in (5,7,11,13,17):
    for d in (32,64,128,256):
        ell=1; a=q%(2*d)
        while a!=1:
            a=a*q%(2*d); ell+=1
        for r in (1,3):
            for _ in range(24):
                I=sorted(rng.sample(range(ell),r)) if ell>=r else list(range(ell))
                A=support_poly(I,d,rng.randint(1,q-1))
                A=shift_poly(A,rng.randrange(d),d,q)
                aa=[A.get(i,0) for i in range(max(A)+1)]
                assert len(poly_gcd([1]+[0]*(d-1)+[1],aa,q))==1
                units+=1

def canonical_short_gap(S,d):
    P=sorted(S)
    H=[((P[(i+1)%len(P)]-x)%d or d,i) for i,x in enumerate(P)]
    gap,i=max(H)
    assert gap>d//2 and [t for t,_ in H].count(gap)==1
    j=P[(i+1)%len(P)]
    return tuple(sorted((x-j)%d for x in P)),j

designed=0
for n in (4,8,16):
    q=5; phases=2*q*(q-1); W=3; d=1
    while d<phases*W*n or d<=2*n:
        d*=2
    occupied=Counter()
    seen=set()
    shapes=Counter()
    for I in list(combinations(range(n),3))+[(i,) for i in range(n)]:
        A=support_poly(I,d,1)
        shape,j=canonical_short_gap(A,d)
        shapes[shape]+=1
        for _ in range(1 if len(I)==3 else W):
            for u in range(1,q):
                for t in range(2*q):
                    nxt=occupied[shape]
                    assert nxt<d
                    shifted=shift_poly({i:u*v for i,v in A.items()},nxt-j,d,q)
                    S=tuple(sorted(shifted))
                    assert S not in seen
                    seen.add(S)
                    occupied[shape]+=1
                    designed+=1
    assert all(x<=n for x in shapes.values())

fullrows=localtable=0
for q in (5,7,11):
    d=32
    h=[113]+[14-min(x,q-x)**2 for x in range(1,q)]
    H=sum(h); kappa=q*(q*h[0]-H)
    for I,C in (((3,),(0,1)),((2,4,13),(0,2)),((0,5,8),(1,3))):
        for vals in product(range(q),repeat=len(I)):
            z=sum(vals)%q
            got=sum(q*h[(u*(c-z))%q] for u in range(1,q) for c in C)
            assert got==2*q*(H-h[0])+kappa*(z in C)
            localtable+=1
        for rep in range(9):
            s=[rng.randrange(q) for _ in range(d)]
            z=sum(s[i] for i in I)%q
            for active in (False,True):
                score=matched=0
                for u in range(1,q):
                    aa=support_poly(I,d,u)
                    z0=mul(aa,s,q)
                    assert z0[0]==u*z%q
                    ts=([u*j%q for j in C for _ in range(q)] if active
                        else [r for r in range(q) for _ in range(2)])
                    for r,c in enumerate(ts):
                        y=[c]+[r%q]*(d-1)
                        t=rng.randrange(d)
                        yy=shift_vector(y,t,q)
                        v=mul(shift_poly(aa,t,d,q),s,q)
                        score+=sum(h[(a-b)%q] for a,b in zip(yy,v))
                        matched+=sum(a==b for a,b in zip(yy,v))
                        fullrows+=1
                B=2*(d-1)*(q-1)
                if active:
                    assert score==B*H+2*q*(H-h[0])+kappa*(z in C)
                    assert matched==B+q*(q-1)*(z in C)
                else:
                    assert score==(B+2*(q-1))*H
                    assert matched==B+2*(q-1)

roundchecks=0
for _ in range(2500):
    n=10; q=rng.choice((5,7,11)); m=rng.randrange(1,15)
    C={I:rng.choice(((0,2),(1,3))) for I in rng.sample(list(combinations(range(n),3)),m)}
    deg=Counter(i for I in C for i in I)
    W=1+max(deg.values())
    z=[rng.randrange(q) for _ in range(n)]
    i=rng.randrange(n)
    def objective(x):
        return W*sum(v<=1 for v in x)+sum(sum(x[j] for j in I)%q in Y for I,Y in C.items())
    if z[i]>1:
        zz=z[:]; zz[i]=0
        assert objective(zz)>objective(z)
        roundchecks+=1
print("PASS units / distinct fixed rows / local tables / complete response rows / Boolean penalties:",
      units,designed,localtable,fullrows,roundchecks)
