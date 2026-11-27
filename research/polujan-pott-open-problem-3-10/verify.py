#!/usr/bin/env python3
"""Recompute the seed permutations and finite regression checks with Python stdlib."""
from itertools import combinations
if not __debug__:
    raise SystemExit("Run without -O")

# For component i, a monomial is its little-endian variable mask.
SEEDS = {
    4: [(2,3,4,5,6), (4,6,8,10,12), (3,9,10), (1,9,4,12,5)],
    5: [(2,3,4,5,6), (1,3,4,6,5), (1,5,2,6,3,24), (16,24,3,5,6), (8,24,3,5,6)],
}


def symmetric(m, y):
    w = y.bit_count()
    p = (w + w * (w-1)//2) & 1
    return y ^ (((1 << m)-1) if p else 0)


def seed(m, y):
    if m == 3:
        return symmetric(m,y)
    return sum((sum((y & t) == t for t in row) & 1) << i
               for i,row in enumerate(SEEDS[m]))


def permutation(m, y):
    if m in (3,4,5):
        return seed(m,y)
    return seed(3,y & 7) | (permutation(m-3,y >> 3) << 3)


def transform(a, walsh=False):
    a = list(a)
    h=1
    while h<len(a):
        for b in range(0,len(a),2*h):
            for i in range(b,b+h):
                j=i+h
                if walsh:
                    a[i],a[j]=a[i]+a[j],a[i]-a[j]
                else:
                    a[j]^=a[i]
        h*=2
    return a


def table(m, p, monomial=0):
    q=1<<m
    return [(((v & p[u^v]).bit_count() & 1) ^
             (bool(monomial) and (u^v) & monomial == monomial))
            for v in range(q) for u in range(q)]


def verify(m, pi, label):
    q=1<<m
    p=[pi(m,y) for y in range(q)]
    assert sorted(p)==list(range(q))
    for i in range(m):
        coord=transform((x>>i)&1 for x in p)
        assert all(not v or j.bit_count()<=2 for j,v in enumerate(coord))
        assert not(p[0]>>i & 1 or p[1<<i]>>i & 1)
        assert all(not (p[(1<<i)|(1<<j)]>>i & 1) for j in range(m) if i!=j)
    f=table(m,p)
    f_anf=transform(f)
    assert {j.bit_count() for j,v in enumerate(f_anf) if v}=={3}
    if m<=7:
        assert {abs(x) for x in transform((1-2*x for x in f),True)}=={q}
        # Independently check each possible basis monomial of the offset.
        off_count=0
        for I in combinations(range(m),3):
            monomial=sum(1<<i for i in I)
            g = transform((((u^v)&monomial)==monomial)
                          for v in range(q) for u in range(q))
            expected={sum(1<<(i+(m if v>>j&1 else 0)) for j,i in enumerate(I))
                      for v in range(8)}
            assert {i for i,x in enumerate(g) if x}==expected
            off_count+=1
        # Exercise the actual Walsh spectrum after a nonzero cubic offset too.
        assert {abs(x) for x in transform((1-2*x for x in table(m,p,7)),True)}=={q}
        print(f"{label} m={m}: Walsh +/-{q}; {off_count} offset monomials")
    print(f"{label} m={m}: permutation with {sum(f_anf)} cubic terms and no other terms")
    if m in (4,5):
        print("  images:",",".join(map(str,p)))


def main():
    for m in (3,4,5,6,8,9):
        verify(m,permutation,"product/seed")
    for m in (3,7):
        q=1<<m
        assert all(symmetric(m,symmetric(m,y))==y for y in range(q))
        verify(m,symmetric,"symmetric involution")
    p=[symmetric(5,y) for y in range(32)]
    assert len(set(p))==16 and p[0]==p[-1]==0
    assert len(set(seed(5,y) for y in range(32)))==32
    bad=lambda m,y:y
    identity_table=table(3,[bad(3,y) for y in range(8)])
    assert {j.bit_count() for j,v in enumerate(transform(identity_table)) if v}=={1,2}
    print("PASS: wrong residue collapses complement pairs; identity has linear and quadratic terms, not cubic")


if __name__=="__main__":
    main()
