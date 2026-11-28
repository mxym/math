#!/usr/bin/env python3
"""Exact finite trace-cell, collision, and partial-trace checks."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from random import Random
rng=Random(293)

collisions=0
for q,n in ((3,2),(5,2),(7,2),(3,3)):
    G=list(product(range(q),repeat=n))
    for _ in range(22):
        raw=[rng.randrange(1,20) for s in G]
        p=[F(x,sum(raw)) for x in raw]
        V=F(0)
        for u in G:
            C=[F(0)]*q
            for s,w in zip(G,p):
                C[sum(a*b for a,b in zip(u,s))%q]+=w
            V+=sum((w-F(1,q))**2 for w in C)
            collisions+=1
        assert V/len(G)==(1-F(1,q))*sum(w*w for w in p)

trace_cells=0
for q,n in ((3,1),(5,1),(7,1),(3,2),(5,2)):
    K=list(product(range(q),repeat=n))
    zero=(0,)*n
    c0=next(a for a in range(1,q) if a not in {b*b%q for b in range(q)})
    def add(a,b): return tuple((u+v)%q for u,v in zip(a,b))
    def mul(a,b):
        if n==1: return (a[0]*b[0]%q,)
        return ((a[0]*b[0]+c0*a[1]*b[1])%q,(a[1]*b[0]+a[0]*b[1])%q)
    def tr(a): return (n*a[0])%q
    triples=list(product(K,K,K[1:])) if n==1 else [
        (rng.choice(K),rng.choice(K),rng.choice(K[1:])) for _ in range(95)]
    for a,b,c in triples:
        x0=next(x for x in K if add(b,mul(c,x))==zero)
        a0=tr(mul(a,x0))
        hist=Counter(tr(add(add(mul(a,x),mul(b,y)),mul(c,mul(x,y))))
                     for x,y in product(K,repeat=2))
        M=len(K)
        assert set(hist)==set(range(q))
        assert all(hist[j]==(M*M-M)//q+(M if j==a0 else 0) for j in range(q))
        trace_cells+=1

def mat_inverse(a):
    n=len(a)
    B=[list(row)+[F(int(i==j)) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        i=next(i for i in range(j,n) if B[i][j])
        B[i],B[j]=B[j],B[i]
        z=B[j][j]
        B[j]=[y/z for y in B[j]]
        for i in range(n):
            if i!=j:
                z=B[i][j]
                B[i]=[x-z*y for x,y in zip(B[i],B[j])]
    return [row[n:] for row in B]

weighted=0
for M,B in product((2,3,4),(2,3)):
    D=M*B
    for _ in range(40):
        rows=[[rng.randrange(-3,4) for j in range(D)] for k in range(5)]
        R=[[F(sum(v[i]*v[j] for v in rows)+int(i==j)) for j in range(D)] for i in range(D)]
        Z=sum(R[i][i] for i in range(D))
        R=[[a/Z for a in row] for row in R]
        tb=[[sum(R[m*B+i][m*B+j] for m in range(M)) for j in range(B)] for i in range(B)]
        ti=mat_inverse(tb)
        Q=sum(M*R[i][m*B+a]*ti[a][b]*R[m*B+b][i]
              for i,m,a,b in product(range(D),range(M),range(B),range(B)))
        assert Q<=M*M
        weighted+=1

print("PASS exact random-query collisions / bilinear trace cells / weighted trace:",
      collisions,trace_cells,weighted)
