#!/usr/bin/env python3
"""Exact coefficient and incidence audit for Lieb dominance on A6."""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import comb

if not __debug__:
    raise RuntimeError("run ordinary Python without -O")

V = tuple(range(6))
FULL = frozenset(V)
PERMS = tuple(permutations(V))
IDENTITY = V
EDGES = tuple(combinations(V, 2))
MATCH2 = tuple(frozenset(e) for e in combinations(EDGES, 2) if len(set(e[0]+e[1])) == 4)
MATCH3 = tuple(frozenset(e) for e in combinations(EDGES, 3) if len(set(e[0]+e[1]+e[2])) == 6)
SUBS = {j: tuple(map(frozenset, combinations(V,j))) for j in range(1,6)}

def cycles(p):
    todo = set(V)
    out = []
    while todo:
        a = min(todo)
        c = [a]
        while p[c[-1]] != a:
            c.append(p[c[-1]])
        todo.difference_update(c)
        out.append(tuple(c))
    return tuple(out)

def parity(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1,len(p)))

def comp(a,b):
    return tuple(a[b[i]] for i in V)

def inv(a):
    return tuple(a.index(i) for i in V)

def typ(p):
    cs = cycles(p)
    s = ''.join(map(str,sorted(map(len,cs), reverse=True)))
    if s == "51":
        q = max(cs,key=len) + min(cs,key=len)
        s += "+" if parity(q) == 1 else "-"
    return s

def cycle_edges(c):
    return tuple(tuple(sorted((a,b))) for a,b in zip(c,c[1:]+c[:1]))

def charge(p):
    # The eleven generators in the proof. Each term is its coefficient on m_p.
    ty=typ(p)
    m=sum(i!=p[i] for i in V)
    f=6-m
    sg=parity(p)
    support={i for i in V if p[i]!=i}
    isD=int(ty=="2211")
    isM=int(ty=="222")
    s2=lambda U: parity(tuple(p[i] for i in sorted(U)))
    F=sum(sg*(int(support.isdisjoint((i,j)))-int(i not in support))
          for i in V for j in V if i!=j)
    cols=[Q(F,30)]
    for j in (1,2,3):
        cols.append(Q(sum(sum(p[i] not in I for i in I)==1 for I in SUBS[j]),comb(6,j)))
    r=sum((1-s2(I))*(1-s2(FULL-I)) for I in SUBS[2] if frozenset(p[i] for i in I)==I)
    cols.append(Q(r,15))
    cols.extend((int(ty=="3111")+Q(2,3)*int(ty=="21111")-Q(2,3)*isD,
                 int(ty=="33")+Q(4,9)*isD,
                 int(ty=="51-")+Q(8,5)*isD,
                 -int(ty=="51+")+Q(8,5)*isD,
                 8*isM-int(ty=="6"),
                 int(ty=="321")+Q(4,3)*isD))
    # Independently count a one-exit subset by one contiguous proper run on
    # one cycle; all other cycles must be wholly inside or wholly outside.
    ls=tuple(map(len,cycles(p)))
    assert cols[0] == Q(-sg*f*m,30)
    for j in (1,2,3):
        good=0
        for k,h in enumerate(ls):
            rest=ls[:k]+ls[k+1:]
            for mask in range(1<<len(rest)):
                a=j-sum(t for i,t in enumerate(rest) if mask>>i&1)
                if 0<a<h:
                    good+=h
        assert cols[j] == Q(good,comb(6,j))
    assert cols[4] == (Q(4*ls.count(2),15) if sg==1 else 0)
    return tuple(cols)

def check_coefficients():
    want = {
        "111111":0, "21111":Q(9,10), "2211":1, "222":1, "3111":Q(9,8),
        "321":1, "33":Q(9,8), "411":1, "42":1, "51+":Q(319,400),
        "51-":Q(431,400), "6":1,
    }
    num=(18000,47292,23010,1580,7275,24924,6504,7800,7880,970,844)
    counts=Counter()
    seen={}
    for p in PERMS:
        k=typ(p)
        cp=charge(p)
        counts[k]+=1
        if k in seen:
            assert cp==seen[k]
        else:
            seen[k]=cp
        assert sum(Q(a,56000)*b for a,b in zip(num,cp))==want[k]
    assert counts == Counter({"111111":1,"21111":15,"2211":45,"222":15,"3111":40,
                              "321":120,"33":40,"411":90,"42":90,"51+":72,"51-":72,"6":120})
    for k in sorted(seen):
        print(k,counts[k],*(str(x) for x in seen[k]),"=>",want[k])
    print("Exact decomposition:",len(PERMS),"permutation coefficients")

def check_incidence():
    assert len(MATCH2)==45 and len(MATCH3)==15
    # Verify the two 5-cycle classes by actual conjugation, not cycle strings.
    even=[p for p in PERMS if parity(p)==1]
    for s in ("51+","51-"):
        cls={p for p in PERMS if typ(p)==s}
        a=next(iter(cls))
        assert len(cls)==72 and {comp(g,comp(a,inv(g))) for g in even}==cls
        assert {inv(p) for p in cls}==cls
        hits=Counter()
        for p in cls:
            c=max(cycles(p),key=len)
            es=cycle_edges(c)
            ways=Counter()
            for i in range(5):
                path=(es+es)[i+1:i+5]
                ways[frozenset(path[::2])]+=1
                ways[frozenset(path[1::2])]+=1
            assert len(ways)==5 and set(ways.values())=={2}
            hits.update(ways.keys())
        assert set(hits)==set(MATCH2) and set(hits.values())=={8}
    triples={tuple(sorted(I)) for I in SUBS[3]}
    pair33,pair32,hex6=Counter(),Counter(),Counter()
    for t in triples:
        T=frozenset(t)
        W=tuple(sorted(FULL-T))
        if t<W:
            for x in combinations(t,2):
                for y in combinations(W,2):
                    pair33[frozenset((x,y))]+=1
        for x in combinations(t,2):
            for y in combinations(W,2):
                pair32[frozenset((x,y))]+=1
    assert set(pair33)==set(pair32)==set(MATCH2)
    assert set(pair33.values())=={2} and set(pair32.values())=={4}
    for p in PERMS:
        if typ(p)=="6":
            e=cycle_edges(cycles(p)[0])
            hex6[frozenset(e[::2])]+=1
            hex6[frozenset(e[1::2])]+=1
    assert set(hex6)==set(MATCH3) and set(hex6.values())=={16}
    print("Incidences: 5+/- = 8, 3+3 = 2, 3+2 = 4, oriented 6 = 16")

if __name__=="__main__":
    check_coefficients()
    check_incidence()
