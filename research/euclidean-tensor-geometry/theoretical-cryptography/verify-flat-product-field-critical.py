#!/usr/bin/env python3
"""Exact finite moments for the flat-product field hashing theorem."""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from math import factorial, prod


def rank2(columns):
    piv={}
    for x in columns:
        while x:
            b=x.bit_length()-1
            if b not in piv:
                piv[b]=x
                break
            x^=piv[b]
    return len(piv)


def falling(z,k):
    return prod(range(z-k+1,z+1)) if z>=k else 0


def small_poisson_diagrams():
    # A non-affine block of size four; n=1,2 and binary k=1,2.
    S=(0,1,2,4)
    count=0
    for n,k in ((1,1),(2,2)):
        D=3*n
        points=[sum(x<<(3*i) for i,x in enumerate(v))
                for v in product(S,repeat=n)]
        for orders in ((3,),(2,1),(1,2)):
            ell=len(orders)
            rhs=F(0)
            for groups in product(*(list(permutations(points,r)) for r in orders)):
                tagged=[x|(1<<(D+i)) for i,g in enumerate(groups) for x in g]
                rhs+=F(1,2**(k*rank2(tagged)))
                count+=1
            lhs=0
            for rows in product(range(1<<D),repeat=k):
                hist=Counter(sum(((x&a).bit_count()&1)<<i
                                 for i,a in enumerate(rows)) for x in points)
                lhs+=prod(sum(falling(hist.get(y,0),r) for y in range(1<<k))
                          for r in orders)
            assert F(lhs,2**(k*(D+ell)))==rhs
    return count


def gbinom(n,k,b=2):
    if not 0<=k<=n:
        return 0
    num=prod(b**n-b**i for i in range(k))
    den=prod(b**k-b**i for i in range(k))
    assert num%den==0
    return num//den


def test_uniform_rank_law():
    count=0
    for N,M in ((2,2),(3,2),(2,3),(3,4)):
        hist=Counter(rank2(cols) for cols in product(range(1<<M),repeat=N))
        for r in range(min(N,M)+1):
            num=prod((2**N-2**j)*(2**M-2**j) for j in range(r))
            den=prod(2**r-2**j for j in range(r))
            assert hist[r]*den==num
        marks=[sum(F(c,2**(N*M))*gbinom(N-r,k)
                   for r,c in hist.items()) for k in range(N+1)]
        assert marks==[F(gbinom(N,k),2**(M*k)) for k in range(N+1)]
        recovered=[]
        for j in range(N+1):
            z=-F(1,2**j)
            s=sum(2**(r*(r-1)//2)*m*z**r for r,m in enumerate(marks))
            def value(k):
                return prod(1+2**i*z for i in range(k))
            p=(s-sum(m*value(k) for k,m in enumerate(recovered)))/value(j)
            assert p==F(hist[N-j],2**(N*M))
            recovered.append(p)
        count+=sum(hist.values())
    return count


def mul8(x,y):
    out=0
    while y:
        if y&1:
            out^=x
        y>>=1
        x<<=1
        if x&8:
            x^=11  # t^3+t+1
    return out


def trace8(x):
    y=mul8(x,x)
    z=x^y^mul8(y,y)
    assert z in (0,1)
    return z


def structured_additive():
    U=(0,1,2,3)
    E=[a for a in range(8) if all(mul8(a,u) in U for u in U)]
    assert E==[0,1]
    # n=3 blocks, k=2 field output coordinates: binary dimensions 6 and 6.
    def scale(a,w):
        return mul8(a,w&7)|(mul8(a,w>>3)<<3)
    paired=[(w,scale(2,w)) for w in range(64)]
    hist=Counter(rank2(x+y+z) for x,y,z in product(paired,repeat=3))
    assert hist[0]==1  # differs from iid binary 6x6 because sample spaces differ
    count=sum(hist.values())
    assert count==64**3
    D=6
    m1=sum(F(c,count)*gbinom(D-r,1) for r,c in hist.items())
    assert m1==F(63,64)
    m2=sum(F(c,count)*gbinom(D-r,2) for r,c in hist.items())
    pts=list(product(U,repeat=3))[1:]
    tors=Counter()
    for x,y in permutations(pts,2):
        h=1 if any(tuple(mul8(a,u) for u in x)==y for a in range(1,8)) else 2
        tors[h]+=1
    assert tors[1]>0 and m2*6==sum(F(c,64**h) for h,c in tors.items())
    return count


def check_generic_quotient():
    columns=list(product(range(8),repeat=2))
    def pairing(y,w):
        return mul8(y[0],w[0])^mul8(y[1],w[1])
    def map_key(Y,w):
        out=tuple(pairing(y,w) for y in Y)
        return tuple(sum(trace8(mul8(g,e))<<i for i,g in enumerate(out))
                     for e in (1,2,4))
    good=((1,2),(2,3))  # determinant 3+(2*2) is nonzero
    bad=((1,0),(2,0))   # binary independent, field dependent
    assert len({map_key(good,w) for w in columns})==64
    assert sorted(Counter(map_key(bad,w) for w in columns).values())==[8]*8
    return 2*len(columns)


def poisson_tv_identity():
    n=0
    for lam in (F(1,2),F(1),F(3,2),F(2),F(11,4),F(10)):
        k=lam.numerator//lam.denominator
        # The common e^-lambda cancels.
        t=sum((1-F(j,1)/lam)*lam**j/factorial(j) for j in range(k+1))
        assert t==lam**k/factorial(k)
        n+=1
    return n


def main():
    print(f"PASS: {small_poisson_diagrams()} tagged rank rows, "
          f"{test_uniform_rank_law()} iid rank samples, "
          f"{structured_additive()} block-correlated rank samples, "
          f"{check_generic_quotient()} quotient maps and "
          f"{poisson_tv_identity()} exact Poisson TV formulas.")


if __name__=="__main__":
    main()
