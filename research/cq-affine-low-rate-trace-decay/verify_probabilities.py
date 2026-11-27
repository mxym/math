#!/usr/bin/env python3
"""Exact direct scalar distributions and pairwise rare-frequency counting."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod


def char(i,j):
    return -1 if (i&j).bit_count()%2 else 1


def image(A,u):
    ans=0
    for i,a in enumerate(A):
        if u>>i&1: ans^=a
    return ans


def apply(A,x):
    return sum(((a&x).bit_count()%2)<<i for i,a in enumerate(A))


def blocks(x,k,n):
    return tuple((x>>(i*k))&((1<<k)-1) for i in range(n))


def norm_scalar(k,n,r,p):
    q=1<<k;N=q**n;M=1<<r
    W0=tuple(abs(sum(char(a,x)*v for x,v in enumerate(p))) for a in range(q))
    weight=[prod(W0[a] for a in blocks(i,k,n)) for i in range(N)]
    source=[prod(p[a] for a in blocks(i,k,n)) for i in range(N)]
    assert sum(source)==1
    seeds=list(product(range(N),repeat=r))
    pair={key:Counter() for key in combinations(range(1,M),2)}
    marginal={u:Counter() for u in range(1,M)}
    observed=[]
    for A in seeds:
        tv=[F(0)]*M
        for x in range(N): tv[apply(A,x)]+=source[x]
        delta=sum(abs(v-F(1,M)) for v in tv)/2
        coeff=[image(A,u) for u in range(1,M)]
        assert max(weight[a] for a in coeff)/2<=delta<=sum(weight[a] for a in coeff)/2
        for u,a in enumerate(coeff,1):
            marginal[u][a]+=1
        for (u,v),hist in pair.items():
            hist[(coeff[u-1],coeff[v-1])]+=1
        observed.append((delta,coeff))
    for hist in marginal.values():
        assert len(hist)==N and set(hist.values())=={len(seeds)//N}
    for hist in pair.values():
        assert len(hist)==N**2 and set(hist.values())=={len(seeds)//(N*N)}
    mean=sum(item[0] for item in observed)/len(seeds)
    U=F(M-1,2)*F(sum(W0),q)**n
    assert mean<=U
    if r==1: assert mean==U
    T_sets=[frozenset(range(N)),frozenset({0}),frozenset(range(min(N,3)))]
    T_sets += [frozenset(i for i,v in enumerate(weight) if v>=a) for a in sorted(set(weight))]
    for T in set(T_sets):
        mu=F((M-1)*len(T),N)
        mt=sum(weight[a] for a in T)/sum(weight)
        maxm=F(0)
        unq=F(0)
        for _,coeff in observed:
            hits=[weight[a] for a in coeff if a in T]
            maxm+=max(hits,default=0)/2
            unq+=hits[0]/2 if len(hits)==1 else 0
        assert maxm/len(seeds)>=U*mt/(1+mu)
        assert unq/len(seeds)>=U*mt*max(0,1-F((M-2)*len(T),N))
    return len(seeds),W0,mean,U


cases=[(1,1,1,(F(4,5),F(1,5))),
       (1,3,1,(F(4,5),F(1,5))),
       (1,4,3,(F(2,3),F(1,3))),
       (2,1,2,(F(8,16),F(4,16),F(3,16),F(1,16))),
       (2,2,2,(F(8,16),F(4,16),F(3,16),F(1,16))),
       (2,2,2,(F(1,4),)*4)]
for k,n,r,p in cases:
    count,S,mean,U=norm_scalar(k,n,r,p)
    print(f"Direct scalar laws: k={k} n={n} r={r} {count} matrices, Fourier norms {','.join(map(str,S))}, mean {mean}, sum bound {U}")

# The output shift matters for strong triple independence, although it
# does not change the distance. Direct distributions at every input triple.
N=8;r=2;M=1<<r
only_A=list(product(range(N),repeat=r))
for tr in combinations(range(N),3):
    h=Counter(tuple(apply(A,x)^c for x in tr)
              for A in only_A for c in range(M))
    assert len(h)==M**3 and set(h.values())=={4}
assert all(apply(A,0)==0 for A in only_A)
# Removing the rank-zero seed invalidates the exact one-bit mean
# on uniform input: every nonzero projection is then exactly balanced.
assert all(sum(apply((a,),x) for x in range(8))==4 for a in range(1,8))
print("All 56 strong-independence triples; negative controls: zero input without shift, and rank-filter bias")

# Exact integer certificates for the gap to all four-wise collision laws
# at R=1/4 and pure-state trace separation s=1/5.
assert 6**12<2**9*5**10
assert 6**8<2**3*5**8
print("Positive-rate pure-state example: both exponential comparisons verified by integer powers")
