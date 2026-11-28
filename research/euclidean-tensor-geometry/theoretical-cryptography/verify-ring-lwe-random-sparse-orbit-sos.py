#!/usr/bin/env python3
"""Exact small read-orbit and local-character proof checks, not a solver."""
from fractions import Fraction as F
from itertools import combinations, product
from random import Random

rng=Random(19)

def shifted(A,h,q):
    d=len(A); out=[0]*d
    for j,a in enumerate(A):
        k=j+h; out[k%d]=a*(-1 if k>=d else 1)%q
    return tuple(out)

distributions=reads=0
for q,d,k in ((2,2,2),(3,2,2),(5,2,2),(2,4,1),(3,4,1)):
    p=F(1,3)
    basis=list(product(range(k),range(d)))
    src=[]
    for x in product(range(q),repeat=k*d):
        prob=F(1)
        for a in x:
            prob*=(p/q if a else 1-p+p/q)
        src.append((x,prob))
    assert sum(w for x,w in src)==1
    for ell in range(1,min(4,k*d)+1):
        for S in combinations(basis,ell):
            C=[rng.randrange(1,q) for _ in S]
            usage=[0]*(k*d)
            for j in range(d):
                indices=[i*d+((j-h)%d) for i,h in S]
                assert len(set(indices))==ell
                for v in indices: usage[v]+=1
            assert max(usage)<=ell
            reads+=d
            stats=[F(0) for j in range(d)]
            for x,w in src:
                u=[0]*d
                for (i,h),t in zip(S,C):
                    a=shifted(x[i*d:(i+1)*d],h,q)
                    u=[(b+t*c)%q for b,c in zip(u,a)]
                for j,a in enumerate(u):
                    if a: stats[j]+=w
            assert all(r==(1-F(1,q))*(1-(1-p)**ell) for r in stats)
            distributions+=len(stats)

def scale(a,c,q): return tuple((c*x)%q for x in a)
def plus(a,b,q): return tuple((x+y)%q for x,y in zip(a,b))
def supp(a): return sum(bool(x) for x in a)
def closure(data,q,w):
    data=set(data)
    while True:
        olds=set(data)
        for a,b in olds:
            for c in range(q):
                data.add((scale(a,c,q),c*b%q))
            for v,t in olds:
                x=plus(a,v,q)
                if supp(x)<=w:
                    data.add((x,(b+t)%q))
        if data==olds: return data

moments=compatibility=0
for q in (2,3,5,7):
    # Oriented incidence: the first four equations sum to the zero
    # vector but their constants do not. Any two distinct vertex rows
    # have four uncancelled coordinates, too wide for this local test.
    G=list(combinations(range(4),2))
    n=len(G)+1
    V=[tuple(((1 if v==i else -1 if v==j else 0)%q) for i,j in G)+(0,)
       for v in range(4)]
    extra=(0,)*(n-1)+(1,)
    zero=(0,)*n
    assert tuple(sum(x[j] for x in V)%q for j in range(n))==zero
    axioms=list(zip(V,(1,0,0,0)))+[(extra,0),(zero,0)]
    D=dict(closure(axioms,q,3))
    assert D[zero]==0 and len(D)==len(closure(axioms,q,3))
    indices={zero}
    for i in range(n):
        u=tuple(int(j==i) for j in range(n))
        indices.update(scale(u,c,q) for c in range(1,q))
    while indices:
        v=next(iter(indices))
        block={u for u in indices if plus(u,scale(v,-1,q),q) in D}
        right={u:D[plus(u,scale(v,-1,q),q)] for u in block}
        for x,y in product(indices,repeat=2):
            if x not in block: continue
            diff=plus(y,scale(x,-1,q),q)
            if y in block:
                assert D[diff]==(right[y]-right[x])%q
            else:
                assert diff not in D
            moments+=1
        indices-=block
    for v,t in axioms:
        for i in range(n):
            e=tuple(int(j==i) for j in range(n))
            for c in range(q):
                for l in range(q):
                    u=scale(e,c,q)
                    z=plus(u,scale(v,l,q),q)
                    if supp(z)<=3:
                        assert (u in D)==(z in D)
                        if u in D:
                            assert D[z]==(D[u]+l*t)%q
                        compatibility+=1

print("PASS exact shift marginals / read counts / rank-one phase classes / local shifts:",
      distributions,reads,moments,compatibility)
