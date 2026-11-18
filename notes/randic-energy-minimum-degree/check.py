"""Exhaustive exact checks up to six labeled vertices; sampling is not a proof."""
from fractions import Fraction as Q
from itertools import combinations
from math import lcm
from collections import Counter
cnt=Counter()
for n in range(3,7):
    edges=list(combinations(range(n),2)); M=lcm(*range(1,n))
    for mask in range(1<<len(edges)):
        N=[set() for _ in range(n)]
        for j,(a,b) in enumerate(edges):
            if mask>>j&1:N[a].add(b); N[b].add(a)
        d=list(map(len,N))
        reached={0}; stack=[0]
        while stack:
            vs=N[stack.pop()]-reached;reached.update(vs);stack.extend(vs)
        if len(reached)!=n:continue
        P=[[M//d[i] if j in N[i] else 0 for j in range(n)] for i in range(n)]
        T=[[sum(P[i][k]*P[k][j] for k in N[i]) for j in range(n)] for i in range(n)]
        t2=sum(T[i][i] for i in range(n));t4=sum(T[i][j]*T[j][i] for i in range(n) for j in range(n))
        upper9=2*n*M**4+11*t2*M*M-4*t4
        assert upper9<=(6*n+2*d.count(1))*M**4
        if min(d)>=2: assert upper9<=6*n*M**4
        cnt[(n,'connected')]+=1
        if min(d)>=2:cnt[(n,'leafless')]+=1
print(cnt)
for d in range(2,1001):
    a2=Q(d-1,d*d); m=Q(1,d*d-d+1)
    assert m+(1-m)*a2==Q(1,d)
    assert m+(1-m)*a2**2==Q(2*d-1,d**3)
print('Two moment identities tested for every integer degree 2–1000.')
