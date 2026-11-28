#!/usr/bin/env python3
"""Independent subset-rank and dealer-port comparisons in binary and scalar coordinates."""
from itertools import combinations


def bf_rank(bits):
    # Elimination in the bit representation of ambient vectors; no slope code.
    piv={}
    for b in bits:
        while b:
            p=b.bit_length()-1
            if p not in piv:
                piv[p]=b
                break
            b ^= piv[p]
    return len(piv)


def mul(a,b):
    # F8 via u^3+u^2+1 (not the scalar encoding used when searching the examples).
    c=0
    for _ in range(3):
        c ^= a if b&1 else 0
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 13
    return c


def sf_rank(vectors):
    # Incrementally create the full scalar span (ambient dimension only three).
    values={0}
    for v in vectors:
        if v in values:
            continue
        m={sum(mul(a,(v>>(3*i))&7)<<(3*i) for i in range(3)) for a in range(8)}
        values={x^y for x in values for y in m}
    return {1:0,8:1,64:2,512:3}[len(values)]


def block(a,b,c):
    return tuple(x+(y<<3)+(z<<6) for x,y,z in zip(a,b,c))


def scalar(a,b,c):
    return a+(b<<3)+(c<<6)


zz=(0,0,0)
ii=(1,2,4)


def all_ranks(B,F):
    assert len(B)==len(F)
    N=len(B)
    r=[]
    for mask in range(1<<N):
        a=bf_rank(x for i in range(N) if mask >> i &1 for x in B[i])
        b=sf_rank(F[i] for i in range(N) if mask >> i &1)
        assert a==3*b
        r.append(b)
    q=0
    for dealer in range(N):
        if r[1<<dealer] == 0:
            continue
        for mask in range(1<<N):
            if mask >> dealer & 1:
                continue
            # A different test for reconstructability: every binary vector
            # of the dealer block must lie in the coalition binary span.
            base=[x for i in range(N) if mask >> i &1 for x in B[i]]
            h=bf_rank(base)
            covered=all(bf_rank(base+[x])==h for x in B[dealer])
            assert covered == (r[mask] == r[mask|1<<dealer])
            q+=1
    return len(r),q


def noncommuting_examples():
    # Concrete binary affine data for the two ordered spread classes; these are
    # direct matrices, not generated with the slope or commuting checks.
    data=[
        ((6,3,1),(4,5,2),[
          ((0,0,0),(6,3,1)),((0,0,0),(4,5,2)),((4,6,7),(0,0,0)),
          ((3,4,1),(0,0,0)),((1,2,4),(1,2,4)),((2,5,6),(3,7,2)),((6,3,7),(7,1,3))]),
        ((7,3,1),(6,7,2),[
          ((0,0,0),(7,3,1)),((0,0,0),(6,7,2)),((4,6,3),(0,0,0)),
          ((3,4,5),(0,0,0)),((1,2,4),(1,2,4)),((2,7,6),(3,5,2)),((5,3,7),(4,1,3))]),
    ]
    collinear=[(0,1),(2,3),(5,6)]  # Extra pairs of one letter.
    n=n1=n2=0
    for X,Y,points in data:
        B=[block(zz,ii,zz),block(ii,zz,zz),block(ii,ii,zz),
           block(ii,X,zz),block(ii,Y,zz),
           block(zz,zz,ii),block(ii,zz,ii),block(zz,ii,ii)]
        a,b=2,3
        iv={x:next(y for y in range(1,8) if mul(x,y)==1) for x in range(1,8)}
        F=[scalar(x,y,0) for x,y in [(0,1),(1,0),(1,1),(1,a),(1,b)]]+[scalar(0,0,1),scalar(1,0,1),scalar(0,1,1)]
        points_f=[(0,a),(0,b),(iv[a],0),(iv[b],0),(1,1),(iv[a^1],iv[a^1]^1),(iv[b^1],iv[b^1]^1)]
        for P in [()]+[(i,) for i in range(7)]+collinear:
            k,l=all_ranks(B+[block(*points[i],ii) for i in P],F+[scalar(*points_f[i],1) for i in P])
            n+=1;n1+=k;n2+=l
        for i,j in combinations(range(7),2):
            if (i,j) in collinear:
                continue
            # The span of the two outside points and a labelled direction
            # can witness partial rank, forbidding this pair in the matroid.
            x,y=block(*points[i],ii),block(*points[j],ii)
            rankset={bf_rank(x+y+z) for z in B[:5]}
            assert rankset.intersection((7,8))
    return n,n1,n2


def comm_examples():
    # A scalar representation with long line and extra rank-defining
    # collinearity, plus duplicates and a loop.
    L=[(0,1,0)]+[(1,a,0) for a in (0,1,2,3,4,5)]
    F=L+[(0,0,1),(1,0,1),(0,1,1),(2,2,1),(0,0,0),(1,2,0)]
    s=lambda a: tuple(mul(a,b) for b in ii)
    B=[block(*map(s,v)) for v in F]
    return all_ranks(B,[scalar(*v) for v in F])


if __name__ == '__main__':
    n,a,b=noncommuting_examples()
    c,d=comm_examples()
    print(f"PASS maximal-five realizations: {n} instances, {a} subset ranks, {b} dealer events")
    print(f"PASS scalar-field control with loop and parallel element: {c} subset ranks, {d} dealer events")
