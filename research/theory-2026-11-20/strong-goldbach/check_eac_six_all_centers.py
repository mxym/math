"""Exact finite controls for EACSixAllCenters; no search in the even center."""
from itertools import combinations
from math import comb

def require(test, msg):
    if not test:
        raise RuntimeError(msg)

def components_and_bip(n, edges):
    nb = [set() for _ in range(n)]
    for i,j in edges:
        nb[i].add(j); nb[j].add(i)
    color = {}
    results = []
    for initial in range(n):
        if initial in color:
            continue
        color[initial] = 0
        comp = [initial]; good = True
        for i in comp:
            for j in nb[i]:
                if j not in color:
                    color[j] = 1 - color[i]; comp.append(j)
                elif color[i] == color[j]:
                    good = False
        results.append((sorted(comp),good))
    return results

def finite():
    # Star labels are [n,6); outside vertices [0,n), all possible distinct
    # labelled non-star edges including loops. Edge counts recover six rows.
    ledger = {}
    for m in range(2,7):
        n=6-m
        edges=[(i,j) for i in range(n) for j in range(i,n)]
        need=7-m
        ngraph=assignment_patterns=0
        for E in combinations(edges,need):
            occupied={v for e in E for v in e}
            if len(occupied) != n:
                continue
            ngraph+=1
            comps=components_and_bip(n,E)
            require(not any(b for _,b in comps),('unexpected bipartite',m,E))
            if m>=4:
                require(m==4 and set(E)=={(0,0),(0,1),(1,1)},('tail',m,E))
            # Choose the unordered set of inputs of these outside edges.
            for U in combinations(range(6),need):
                assignment_patterns+=1
                if any(i<n for i in U):
                    continue
                require(m==4,('no direct row',m,E,U))
                S=set(range(n,6))
                for center in S:
                    leaves=S-{center}
                    known=set(U)&leaves
                    unknown=leaves-known
                    require(len(known)>len(unknown),('known-leaf fallback',U,center))
        ledger[m]=(ngraph,assignment_patterns)
    # All outside graphs at m=2 have five among ten possible edges, excluding
    # a missed vertex by inclusion-exclusion (two misses leave only 3 edges).
    require(ledger[2][0]==comb(10,5)-4*comb(6,5),'m2 count')
    require(ledger[3][0]==comb(6,4),'m3 count')
    require(ledger[4][0]==1 and ledger[5][0]==ledger[6][0]==0,'large stars')
    print('PASS labelled residual cofactor graphs / unordered input subsets:',ledger)

if __name__=='__main__':
    finite()
