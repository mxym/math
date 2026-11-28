#!/usr/bin/env python3
"""Exact conditional channel construction with a circular systematic sampler."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb

def majorant(N, p):
    if len(p) <= N:
        return p+(F(0),)*(N-len(p)), len(p), F(0)
    j, total = 0, F(1)
    while p[j]*(N-j) > total:
        total -= p[j]
        j += 1
    b=total/(N-j)
    return p[:j]+(b,)*(N-j),j,b

def components(N,p,r,b):
    if len(p)<=N:
        return [(F(1),p)]
    # Split [0,m) into consecutive intervals of lengths p_i/b.
    # Each offset u in [0,1) selects the intervals hit by u,u+1,...,u+m-1.
    t=[F(0)]
    for x in p[r:]:
        t.append(t[-1]+x/b)
    assert t[-1]==N-r
    breaks=sorted({F(0),F(1)}|{x%1 for x in t})
    out=[]
    for l,h in zip(breaks,breaks[1:]):
        u=(l+h)/2
        S=[i for i in range(len(t)-1)
           if any(t[i]<=u+j<t[i+1] for j in range(N-r))]
        assert len(S)==N-r
        out.append((h-l,p[:r]+tuple(b if i in S else F(0)
                                     for i in range(len(t)-1))))
    assert sum(a for a,_ in out)==1
    assert all(sum(a*x[i] for a,x in out)==p[i] for i in range(len(p)))
    return out

def plus(x):
    return max(F(0),x)

def check(N, weights):
    p=tuple(F(x,sum(weights)) for x in sorted(weights,reverse=True) if x)
    w,r,b=majorant(N,p)
    assert len(w)==N and sum(w)==1 and sorted(w,reverse=True)==list(w)
    assert all(sum(w[:j])>=sum(p[:j]) for j in range(1,max(N,len(p))+1))
    # Actually build the encoder row (message,key) -> ciphertext probabilities,
    # then forget those conditionals and compute the posterior from the joint law.
    row=defaultdict(list)
    for s,(weight,theta) in enumerate(components(N,p,r,b)):
        keys=tuple(i for i,x in enumerate(theta) if x)
        assert tuple(sorted(theta,reverse=True)[:len(keys)])==w[:len(keys)]
        zs=list(permutations(range(N),len(keys)))
        for z in zs:
            for i,j in zip(keys,z):
                v=weight*theta[i]/len(zs)/(p[i]/N)
                row[(j,i)].append(((s,keys,z),v))
    assert len(row)==N*len(p)
    post=defaultdict(lambda:[F(0)]*N)
    for (m,i),vals in row.items():
        assert sum(v for _,v in vals)==1
        for c,v in vals:
            _,keys,z=c
            assert z[keys.index(i)]==m
            post[c][m]+=p[i]/N*v
    gains=[]
    for a in range(N+1):
        direct=set()
        for A in combinations(range(N),a):
            direct.add(sum(abs(sum(t[j] for j in A)-sum(t)/2)
                           for t in post.values())-abs(F(a,N)-F(1,2)))
        assert len(direct)==1
        gains.extend(direct)
    half=N//2
    closed=2*sum(plus(sum(w[j] for j in A)-F(1,2))
                 for A in combinations(range(N),half))/comb(N,half)
    assert max(gains)==gains[half]==closed
    assert gains==gains[::-1]
    assert gains[:half+1]==sorted(gains[:half+1])
    assert (closed==0)==(sum(w[:half])<=F(1,2))
    if N%2==0:
        assert (closed==0)==(p[0]<=F(1,N))
    if len(p)>N:
        grouped=F(0)
        for j in range(r+1):
            if 0<=half-j<=N-r:
                for S in combinations(range(r),j):
                    grouped+=comb(N-r,half-j)*plus(
                        sum(p[i] for i in S)+(half-j)*b-F(1,2))
        assert 2*grouped/comb(N,half)==closed
    return closed,len(post)

cases=[
    (N,W) for N in range(1,6)
    for W in ((1,), (1,1),(3,1),(4,3,3),(1,1,1),
              (5,3,2,1),(1,1,1,1,1,1),(4,1,1,1,1,1),(6,3,1,1,1,1),
              (1,0,1,0,3),(40,12,12,12,12,12),(40,35,20,2,2,1))
]
outputs=[check(n,w) for n,w in cases]
v1,_=check(4,(40,12,12,12,12,12))
v2,_=check(4,(40,35,20,2,2,1))
assert (v1,v2)==(F(1,10),F(2,15))
v,_=check(3,(4,3,3))
assert v==0
print(f"Rational channels: {len(cases)} laws/dimensions, "
      f"{sum(c for _,c in outputs)} ciphertext tables, all priors and decoders PASS.")
print(f"Equal-support/equal-min-entropy comparison: {v1} versus {v2}; odd zero {v}.")
