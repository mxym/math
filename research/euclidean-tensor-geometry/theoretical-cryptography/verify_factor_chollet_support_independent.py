#!/usr/bin/env python3
"""Literal cross-checks of the order-eleven support and degree identities."""
from itertools import combinations, permutations
from collections import Counter, defaultdict
from fractions import Fraction as F
from math import comb, factorial
from random import Random

if not __debug__:
    raise RuntimeError("run without -O")


def matmul(A,B):
    n=len(A)
    return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def degree_census(n):
    E=list(combinations(range(n),2))
    out=[-1]*(len(E)+1)
    for mask in range(1<<len(E)):
        adj=[0]*n
        for j,(a,b) in enumerate(E):
            if (mask>>j)&1:adj[a]+=1; adj[b]+=1
        m=mask.bit_count()
        out[m]=max(out[m],sum(i*i for i in adj))
    alt=[-1]*(len(E)+1)
    for mask in range(1<<(n-1)):
        G=[[0]*n for _ in range(n)]
        for k in range(1,n):
            if (mask>>(k-1))&1:
                for j in range(k): G[j][k]=G[k][j]=1
        d=list(map(sum,G))
        alt[sum(d)//2]=max(alt[sum(d)//2],sum(x*x for x in d))
    assert out==alt and min(out)>=0
    return 1<<len(E)


def moments(n):
    seed=Random(6349+n)
    E=list(combinations(range(n),2))
    H=[[0]*n for i in range(n)]
    for a,b in E:
        H[a][b]=H[b][a]=seed.randint(-5,5)
    X=[[v*v for v in row] for row in H]
    d=[sum(r) for r in X]
    S=sum(d)//2;R=sum(x*x for x in d)
    Q=sum(X[a][b]**2 for a,b in E)
    H2=matmul(H,H);H3=matmul(H,H2);H4=matmul(H2,H2)
    tr3=sum(H3[i][i] for i in range(n))
    tr4=sum(H4[i][i] for i in range(n))
    Sums=defaultdict(int)
    Pair=defaultdict(int)
    Triples=defaultdict(Counter)
    for p in permutations(range(n)):
        A=[(i,p[i]) for i in range(n) if i!=p[i]]
        m=len(A)
        w=1
        for a,b in A:w*=H[a][b]
        Sums[m]+=w
        for (i,j),(k,l) in combinations(A,2):
            Pair[m]+=X[i][j]*X[k][l]
        for T in combinations(A,3):
            Triples[m][tuple(sorted(T))]+=1
    assert Sums[2]==S
    assert Sums[3]==F(tr3,3)
    assert Sums[4]==F(S*S,2)+F(tr4,4)-R+Q

    D=[sum((-1)**j*comb(m,j)*factorial(m-j) for j in range(m+1)) for m in range(n+1)]
    E2={(a,b):X[a][b] for a,b in E}
    Adj=sum(E2[a]*E2[b] for a,b in combinations(E,2) if set(a)&set(b))
    Dis=sum(E2[a]*E2[b] for a,b in combinations(E,2) if not (set(a)&set(b)))
    assert Adj==F(R,2)-Q and Dis==F(S*S+Q-R,2)
    M=comb(n,2)

    types=0
    arcs=tuple((i,j) for i in range(n) for j in range(n) if i!=j)
    for m in range(2,n+1):
        r=F(D[m-2],D[m]);a=F(2,m-1)-2*r;b=1-r-a
        t=r*Q/M+a*Adj/((n-2)*M)+b*Dis/(3*comb(n,4))
        assert Pair[m]==comb(m,2)*comb(n,m)*D[m]*t
        if m<3:continue
        for T in combinations(arcs,3):
            if len({i for i,j in T})<3 or len({j for i,j in T})<3:
                assert Triples[m][tuple(sorted(T))]==0
                continue
            v=len({y for ij in T for y in ij})
            k=0 if m<v else comb(n-v,m-v)*sum(
                  (-1)**l*comb(m-v,l)*factorial(m-3-l) for l in range(m-v+1))
            assert Triples[m][tuple(sorted(T))]==k
            types+=1
        # Aggregating the cylinders by orientation yields the polynomial used
        # by the exact checker, with the five ordinary undirected support types.
        grouped=defaultdict(set)
        for T,cnt in Triples[m].items():
            if cnt:
                U=tuple(sorted(tuple(sorted(ab)) for ab in T))
                grouped[U].add(T)
        for U,V in grouped.items():
            v=len({i for ab in U for i in ab})
            ways=2 if len(set(U))==2 else {3:2,4:2,5:4,6:8}[v]
            assert len(V)==ways
    return types


def main():
    g=sum(degree_census(n) for n in range(2,7))
    c=sum(moments(n) for n in range(4,8))
    print("INDEPENDENT PASS",g,"ordinary graphs;",c,"fixed-arc completions; exact traces 3/4 and pair moments")

if __name__=="__main__":main()
