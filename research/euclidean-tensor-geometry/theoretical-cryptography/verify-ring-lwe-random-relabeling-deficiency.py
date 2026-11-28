#!/usr/bin/env python3
"""Exact finite checks of list intersection and abstract experiment deficiency bounds."""
from fractions import Fraction as F
from itertools import permutations, product
from math import comb, cos, exp, log, pi
from random import Random

comb_cases=0
for n in range(3,8):
    all_perms=list(permutations(range(n)))
    for j,k in product(range(1,n),repeat=2):
        expected=[F(comb(k,c)*comb(n-k,j-c),comb(n,j))
                  if c<=k and 0<=j-c<=n-k else F(0) for c in range(j+1)]
        actual=[0]*(j+1)
        for p in all_perms:
            actual[sum(p[a]<k for a in range(j))]+=1
        assert [F(x,len(all_perms)) for x in actual]==expected
        for c in range(1,min(j,k)+1):
            assert sum(expected[c:])<=comb(j,c)*F(k,n)**c
            comb_cases+=1

rng=Random(217)
channels=0
for trial in range(800):
    N=6
    labels=list(range(N))
    perm=labels[:]
    rng.shuffle(perm)
    sources,targets=3,4
    def draw(m):
        w=[rng.randrange(1,10) for _ in range(m)]
        return [F(x,sum(w)) for x in w]
    P=[draw(sources) for _ in labels]
    T=[draw(targets) for _ in labels]
    Q=[draw(targets) for _ in range(sources)]
    L1=[set(rng.sample(labels,rng.randint(1,N))) for _ in range(sources)]
    L2=[set(rng.sample(labels,rng.randint(1,N))) for _ in range(targets)]
    hcap=F(rng.randrange(1,7),7)
    Z=[sum(P[s][x] for s in labels) for x in range(sources)]
    post=[[P[s][x]/Z[x] for s in labels] for x in range(sources)]
    e1=sum(P[s][x] for s,x in product(labels,range(sources)) if s not in L1[x])/N
    e2=sum(T[s][y] for s,y in product(labels,range(targets)) if s not in L2[y])/N
    high=sum(P[s][x] for s,x in product(labels,range(sources))
             if post[x][s]>hcap)/N
    budget=max(len({perm[s] for s in u}&v) for u,v in product(L1,L2))
    S=[[sum(P[s][x]*Q[x][y] for x in range(sources)) for y in range(targets)]
       for s in labels]
    sim=sum(S[s][y] for s,y in product(labels,range(targets)) if perm[s] in L2[y])/N
    delta=sum(abs(S[s][y]-T[perm[s]][y])
              for s,y in product(labels,range(targets)))/(2*N)
    assert sim<=e1+high+budget*hcap
    assert delta>=1-e1-e2-high-budget*hcap
    channels+=1

partitions=0
N=6
U=[set(range(0,2)),set(range(2,4)),set(range(4,6))]
V=[set(range(0,3)),set(range(3,6))]
for perm in permutations(range(N)):
    tab=[[sum(perm[s] in v for s in u) for v in V] for u in U]
    opt=F(sum(max(row) for row in tab),N)
    brute=max(F(sum(tab[i][a] for i,a in enumerate(col)),N)
             for col in product(range(len(V)),repeat=len(U)))
    assert opt==brute
    assert 1-opt>=1-F(max(max(row) for row in tab),len(U[0]))
    partitions+=1

mesh_cases=0
for d in (2,4,8,16):
    b=.2/d
    m=d**3
    q=5
    f=lambda y: 1+2*sum(b**(h*h)*cos(2*pi*h*y) for h in range(1,6))
    for i in range(400):
        y=rng.random()
        z=round(y*m)/m
        logs=[log(f(y-a/q)) for a in range(q)]
        grid=[log(f(z-a/q)) for a in range(q)]
        err=max(abs(a-b) for a,b in zip(logs,grid))
        l=log(sum(exp(x) for x in logs)); r=log(sum(exp(x) for x in grid))
        assert abs(l-r)<=err+1e-15
        assert max(abs((a-l)-(b-r)) for a,b in zip(logs,grid))<=2*err+1e-15
        assert err <= 10*b/m
        mesh_cases+=1

print("PASS hypergeometric tails / finite law certificates / deterministic partitions / mesh bounds:",
      comb_cases,channels,partitions,mesh_cases)
