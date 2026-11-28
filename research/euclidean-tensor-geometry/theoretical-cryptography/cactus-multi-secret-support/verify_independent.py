#!/usr/bin/env python3
"""Weighted local rows, unnormalized permutation atlas, and explicit bound."""
from collections import Counter
from itertools import permutations, product


def q_reduction():
    # Edge triples indexed heavy, light 0, light 1.  Weight law is in quarters.
    rows={
        "C": ((0,0,0),),
        "B": ((0,1,1),(1,0,0)),
        "S": ((0,1,0),(0,0,1)),
        "F": ((0,1,2),(0,2,1)),
    }
    privacy=decoding=0
    for d in range(1,6):
        for types in product(rows,repeat=d):
            cases=[]
            for columns in product(*(rows[t] for t in types)):
                old=tuple(zip(*columns))
                weights=Counter(old)
                weights[old[0]]+=1
                new=tuple(tuple((u^col[0]) if t=="B" else
                   (u if t in ("S","F") else 0)
                   for t,col in zip(types,columns)) for u in (0,1))
                cases.append((set(old),weights,set(new),Counter(new)))
            for A,B in product(cases,repeat=2):
                if A[1]==B[1]:
                    assert A[3]==B[3]
                    privacy+=1
                if A[0].isdisjoint(B[0]):
                    assert A[2].isdisjoint(B[2])
                    decoding+=1
    return privacy,decoding


def raw_atlas():
    # Use the six full, unnormalized local maps on a triangle.  Record
    # every domain accepted by those maps, for each rigid mask.
    p=tuple(permutations(range(3)))
    pair=tuple(product(p,repeat=2))
    atlas={a:set() for a in (3,5,6,7)}
    word=tuple(product((0,1),repeat=3))
    for mapping in product(pair,repeat=3):
        good=sum((1<<i) for i,(f,g) in enumerate(mapping) if
                 all(a!=b for a,b in zip(f,g)))
        rs=[r for r in atlas if r & ~good==0]
        if not rs:
            continue
        mask=0
        for i,w in enumerate(word):
            f,g,h=(mapping[j][w[j]] for j in range(3))
            if all(h[g[f[s]]]==s for s in range(3)):
                mask|=1<<i
        for r in rs:
            sub=mask
            while sub:
                atlas[r].add(sub)
                sub=(sub-1)&mask
    return word,atlas


def signed_atlas(word):
    # Independent formula on affine signs/shifts, fixing a baseline per domain.
    S=tuple(product((1,-1),range(3)))
    atlas={a:set() for a in (3,5,6,7)}
    for r in atlas:
        for maps in product(S,repeat=3):
            if any(r>>i&1 and (s!=1 or t==0) for i,(s,t) in enumerate(maps)):
                continue
            for base in word:
                mask=0
                for i,w in enumerate(word):
                    a,t=1,0
                    for j,(sg,sh) in enumerate(maps):
                        if base[j]!=w[j]:
                            a,t=sg*a,(sg*t+sh)%3
                    if (a,t)==(1,0):
                        mask|=1<<i
                sub=mask
                while sub:
                    atlas[r].add(sub)
                    sub=(sub-1)&mask
    return atlas


def explicit_four():
    # Shared vertex a, triangle a,b,c, square a,d,e,f.  These two paths
    # and the extra duplicated field on a-f cover the entire six-cube.
    T={"000","011","101","110"}
    S={"0000","0111","1001","1010","1100"}
    assert len({t+s[1:] for t in T for s in S if t[0]==s[0]})==10
    assert not any(all(sum(i*int(j) for i,j in zip(p,x))%2==0 for x in S)
        for p in product((0,1),repeat=4) if any(p))
    assert all((-int(x[0])+sum(map(int,x[1:])))%3==0 for x in S)

    views={}
    for x in product(range(2),repeat=6):
        a,b,c,d,e,f=x
        local=[Counter() for _ in x]
        for R,U in product(range(2),repeat=2):
            w={(1,2):(R,U), (0,2):(R^c,), (0,1):(U^b,),
                (0,5):(R^c^a,U^b), (4,5):(R^c^a^f,),
                (3,4):(R^c^a^f^e,U^b^a^d), (0,3):(U^b^a,)}
            for v in range(6):
                view=tuple(sh for E,sh in w.items() if v in E)
                local[v][view]+=1
        for v in range(6):
            assert views.setdefault((v,x[v]),local[v])==local[v]
    for v in range(6):
        assert set(views[v,0]).isdisjoint(views[v,1])


if __name__=="__main__":
    law,supp=q_reduction()
    print(f"INDEPENDENT: Q to uniform bit checked on {law} equal-law and {supp} disjoint-support local pairs")
    word,A=raw_atlas()
    assert signed_atlas(word)==A
    assert sum(len(x) for x in A.values())>0
    even=sum(1<<i for i,w in enumerate(word) if sum(w)%2==0)
    assert even not in A[6]
    print("INDEPENDENT: 4 triangle rigid masks x 255 domains; raw and normalized group tests agree")
    explicit_four()
    print("INDEPENDENT: cross-block lower certificates and explicit 256-row four-state full-cube scheme PASS")
