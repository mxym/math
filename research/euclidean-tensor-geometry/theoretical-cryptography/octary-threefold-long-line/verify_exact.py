#!/usr/bin/env python3
"""Exact matrix operation check of field shadows, the spread dichotomy and affine table."""
from itertools import product, permutations, combinations

Z = (0,0,0)
I = (1,2,4)
V = None


def apply(A, x):
    return (A[0] if x & 1 else 0) ^ (A[1] if x & 2 else 0) ^ (A[2] if x & 4 else 0)


def add(A,B):
    return tuple(a^b for a,b in zip(A,B))


def prod(A,B):
    return tuple(apply(A,b) for b in B)


GL = {A for A in product(range(8), repeat=3) if len({apply(A,x) for x in range(8)}) == 8}
INV = {A: tuple({apply(A,x):x for x in range(8)}[i] for i in I) for A in GL}
UNITS = {A for A in GL if add(A,I) in GL}


def field_of(X):
    out = {Z}
    g = I
    for _ in range(7):
        out.add(g)
        g = prod(g,X)
    assert g == I and len(out) == 8
    return out


def compatibles(X,Y):
    allowed = {Z,I,X,Y}
    return {A for A in product(range(8),repeat=3)
            if all(A==B or add(A,B) in GL for B in allowed)}


def slope(P,Q):
    A,B=(add(P[i],Q[i]) for i in (0,1))
    if A == Z and B in GL:
        return V
    if A in GL:
        return prod(B,INV[A])
    return 'not a compatible direction'


def af_table(X,Y):
    D=(V,Z,I,X,Y)
    anchors=((Z,Z),(I,Z),(Z,I))
    candidates=sorted((tuple(D.index(slope(P,Q)) for Q in anchors),P)
                      for P in product({Z,I}|UNITS,repeat=2)
                      if all(slope(P,Q) in D for Q in anchors))
    expected=[]
    for t,a in ((X,3),(Y,4)):
        u=INV[add(t,I)]
        expected += [((0,a,0),(Z,t)),((1,1,a),(INV[t],Z)),((a,2,2),(u,add(u,I)))]
    expected += [((2,0,1),(I,I))]
    assert sorted(expected)==candidates
    edges=[]
    for (a,P),(b,Q) in combinations(candidates,2):
        c=slope(P,Q)
        if c in D: edges.append((a,b,D.index(c)))
    assert edges==[((0,3,0),(0,4,0),0),((1,1,3),(1,1,4),1),((3,2,2),(4,2,2),2)]
    return len(candidates),len(edges)


def run():
    assert len(GL)==168 and len(UNITS)==48
    all_pairs={(X,Y) for X,Y in permutations(UNITS,2) if add(X,Y) in GL}
    off=set()
    same=0
    shadows=0
    for X in UNITS:
        field=field_of(X)
        for Zt in GL-field:
            h=sum(add(Zt,A) in GL for A in field-{Z})
            assert h in (0,2)
            shadows+=1
    for X,Y in all_pairs:
        c=compatibles(X,Y)
        if prod(X,Y)==prod(Y,X):
            assert c==field_of(X)
            same+=1
        else:
            assert c=={Z,I,X,Y}
            off.add((X,Y))
    assert (len(all_pairs),same,len(off))==(576,240,336)
    orbit=0
    tab=ect=0
    while off:
        x,y=min(off)
        os={(prod(prod(g,x),INV[g]),prod(prod(g,y),INV[g])) for g in GL}
        assert len(os)==168 and os <= off
        off-=os
        orbit+=1
        p,e=af_table(x,y)
        tab+=p
        ect+=e
    assert orbit==2 and tab==14 and ect==6
    print(f"PASS field shadows: {shadows} exact compatibility counts; 576 ordered five-set pairs")
    print(f"PASS spread dichotomy: 240 field, 336 maximal; {orbit} normalized noncommuting classes")
    print(f"PASS affine extension table: {tab} candidates and {ect} compatible pairs across representatives")


if __name__ == '__main__':
    run()
