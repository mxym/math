#!/usr/bin/env python3
"""Exact degree profile and repeated-star controls at 24 and 25 edges."""
from functools import cache
from itertools import combinations
from math import comb


def require(test,msg):
    if not test:raise AssertionError(msg)


@cache
def partitions(n,maximum):
    if n==0:return ((),)
    return tuple((h,)+p for h in range(min(n,maximum),0,-1)
                 for p in partitions(n-h,h))


def analyze(m,cap):
    table={}
    for mn in (5,6):
        table[mn]={(p.count(1),sum(comb(x,2) for x in p),p.count(5))
                   for p in partitions(m,m-9)
                   if len(p)>=mn and all(sum(p[:h])<=m-b
                                         for h,b in ((2,5),(3,3),(4,1)))}
    full={(0,0,0)}
    for mn in (5,6,6,6,6,6):
        full={(a+u,b+v,c+w) for a,b,c in full for u,v,w in table[mn]
              if a+u<=cap}
    top=max(b for a,b,c in full)
    candidates=sorted({(b-comb(m,2),c) for a,b,c in full if b>=comb(m,2)})
    counts=(len(table[5]),len(table[6]),len(full))
    print("m, singleton budget, local and combined sizes, S bound, candidates:",
          m,cap,counts,top,candidates)
    return counts,top,candidates


def covered_triples(v,E):
    all_pairs=list(combinations(range(v),2))
    triples=[set(combinations(x,2)) for x in combinations(range(v),3)]
    for k in range(min(E,len(all_pairs))+1):
        if any(all(T.intersection(J) for T in triples)
               for J in combinations(all_pairs,k)):
            return True
    return False


require(analyze(13,11)==((35,30,253),71,[]),"24 edges with m=13")
require(analyze(13,12)==((35,30,291),73,[]),"25 edges with m=13")
info=analyze(14,10)
require(info==((58,50,1318),94,[(0,4),(0,5),(0,6),(1,5),(1,6),(2,6),(3,6)]),
        "24 edges with m=14")
for E,v in info[2]:
    B=comb(E+1,2)
    if (E,v)==(3,6):
        require(covered_triples(v,B),"uncoupled six-star check is intentionally feasible")
        require(all(not any(set(e).issubset(J) for e in combinations(range(4),2))
                    for J in [(0,4,5),(1,4,5),(2,4,5),(3,4,5)]),
                "four-vertex support cannot cover all triples")
    else:
        require(not covered_triples(v,B),"repeated-star cap excludes profile")
print("PASS repeated-star constraints and all degree profiles")
