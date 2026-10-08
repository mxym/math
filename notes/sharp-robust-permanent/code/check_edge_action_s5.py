#!/usr/bin/env python3
"""Exact proof replay: S5 on its ten 2-element subsets (paper, Section 16).

Enumerates all 120 elements and all 100 edge-to-edge marginals.
No floating point or optimization solver is used; all measures are Fraction.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations

G = list(permutations(range(5)))
I = tuple(range(5))
edges = list(combinations(range(5),2))
assert len(G)==120 and len(edges)==10

def cycle_type(g):
    seen=set()
    ls=[]
    for i in range(5):
        if i in seen: continue
        x=i;size=0
        while x not in seen:
            seen.add(x)
            x=g[x];size+=1
        ls.append(size)
    return tuple(sorted(ls,reverse=True))

def image_edge(g,E):
    return tuple(sorted((g[E[0]],g[E[1]])))

def FA(g):
    fixed=adjacent=0
    for E in edges:
        B=image_edge(g,E)
        common=len(set(E).intersection(B))
        fixed+=(common==2)
        adjacent+=(common==1)
    return fixed, adjacent

types=defaultdict(list)
for g in G:
    types[cycle_type(g)].append(g)
table={
    (1,1,1,1,1):(1,10,0,F(4,9)),
    (2,1,1,1):(10,4,6,F(1,9)),
    (2,2,1):(15,2,4,F(1,9)),
    (3,1,1):(20,1,9,F(4,9)),
    (3,2):(20,1,3,F(1,9)),
    (4,1):(30,0,8,F(4,9)),
    (5,):(24,0,5,F(5,18)),
}
assert set(types)==set(table)
for kind,perms in types.items():
    count,fix,adj,w=table[kind]
    assert len(perms)==count
    for g in perms:
        f,a=FA(g)
        assert (f,a)==(fix,adj)
        h=(F(1) if g==I else F(0))-F(f-a,18)
        assert h==w
lo=min(val[3] for val in table.values())
hi=max(val[3] for val in table.values())
assert lo==F(1,9) and hi==F(4,9) and hi-lo==F(1,3)
print('PASS: seven exact conjugacy rows, all 120 dual bounds, range=1/3')

C=set(types[(3,1,1)])
T=set(types[(2,1,1,1)])
P={g:(F(1,3) if g==I else F(0))+(F(2,3*len(C)) if g in C else F(0))
   for g in G}
Q={g:(F(1,len(T)) if g in T else F(0)) for g in G}
assert len(C)==20 and len(T)==10 and not (C & T)
assert sum(P.values())==sum(Q.values())==1
assert not ({g for g in G if P[g]} & {g for g in G if Q[g]})

for E in edges:
    for B in edges:
        p_mass=sum(P[g] for g in G if image_edge(g,E)==B)
        q_mass=sum(Q[g] for g in G if image_edge(g,E)==B)
        assert p_mass==q_mass
print('PASS: 100 exactly matching edge-image marginals')

delta=F(1,24)
u=F(1,len(G))
nu={g:u+delta*(P[g]-Q[g]) for g in G}
assert min(nu.values())>=0 and sum(nu.values())==1
for E in edges:
    for B in edges:
        assert sum(nu[g] for g in G if image_edge(g,E)==B)==F(1,len(edges))
TV=sum(abs(nu[g]-u) for g in G)/2
assert TV==delta
assert nu[I]-u==delta/3
v={g:nu[g]-u for g in G}
assert sum(v[g]*(FA(g)[0]-FA(g)[1]) for g in G)==0
assert sum(v[g]*((F(1) if g==I else 0)-F(FA(g)[0]-FA(g)[1],18))
           for g in G)==nu[I]-u
print('PASS: rational signed law, all 100 uniform marginals, TV and exact 1/3 atom excess')
print('S5 EDGE-ACTION PRIMAL-DUAL CERTIFICATE REPLAY PASSED')
