#!/usr/bin/env python3
"""Exact finite checks of the list sandwich and the rank-one null-subspace comparison."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from random import Random
from math import prod

rng=Random(415)
sandwich=coarsen=0
for n in range(2,8):
    for _ in range(90):
        q=5
        def law(m):
            w=[rng.randrange(1,11) for j in range(m)]
            return [F(x,sum(w)) for x in w]
        pi=law(n)
        reference=law(q)
        P=[law(q) for s in range(n)]
        likelihood=[[u/v for u,v in zip(row,reference)] for row in P]
        joint=[[p*z for z in row] for p,row in zip(pi,likelihood)]
        max_cross=max(F(1),max(sum(a*b*c for a,b,c in zip(likelihood[i],likelihood[j],reference))
                             for i in range(n) for j in range(i)))
        d_feat=[rng.randrange(n//2+1) for _ in range(n)]
        feat=set(d_feat)
        sf={g:sum(pi[s] for s in range(n) if d_feat[s]==g) for g in feat}
        for y in range(q):
            for s in range(n):
                m=sum(joint[v][y] for v in range(n))
                g=d_feat[s]
                mg=sum(joint[v][y] for v in range(n) if d_feat[v]==g)/sf[g]
                actual=m/(sf[g]*mg) # reciprocal of the feature posterior
                sg=min(F(1,sf[g]),max(F(1),F(1,joint[s][y])))
                # The exact multiplicative version of the log-surprisal identity.
                assert sg==max(F(1),joint[s][y])/(sf[g]*max(F(1),joint[s][y]/sf[g]))
                assert actual/sg==m/max(F(1),joint[s][y])*max(F(1),joint[s][y]/sf[g])/mg
                coarsen+=1
        for L in range(1,n+1):
            opt=sum(reference[y]*sum(sorted((joint[s][y] for s in range(n)),reverse=True)[:L])
                    for y in range(q))
            for z in (1,2,3,7):
                hi=sum(reference[y]*joint[s][y] for s,y in product(range(n),range(q))
                       if joint[s][y]*L>z)
                lo=sum(reference[y]*joint[s][y] for s,y in product(range(n),range(q))
                       if joint[s][y]*L>=F(1,z))
                assert hi-max_cross/z <= opt <= lo+F(1,z)
                sandwich+=1

kernels=0
for q,r in ((3,2),(3,3),(5,2)):
    V=list(product(range(q),repeat=r))
    def dot(a,b): return sum(x*y for x,y in zip(a,b))%q
    good=0
    for rows in product(V,repeat=r-1):
        line=[h for h in V if all(dot(a,h)==0 for a in rows)]
        if len(line)!=q: continue
        good+=1;h=line[1]
        assert h!=(0,)*r
        assert {tuple(x*u%q for u in h) for x in range(q)}==set(line)
        assert Counter(dot(a,h) for a in V)=={x:q**(r-1) for x in range(q)}
        c=next(a for a in V if dot(a,h)==1)
        assert all(dot(c,s)==x for x,s in enumerate(tuple(x*u%q for u in h) for x in range(q)))
        kernels+=1
    assert F(good,len(V)**(r-1))==prod(1-F(1,q**(r-i)) for i in range(r-1))

print("PASS finite list bounds / feature identities / full-row-rank null lines:",
      sandwich,coarsen,kernels)
