#!/usr/bin/env python3
"""Exact row cap and public-seed chi-square identities for finite tables."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from random import Random


def pref(n):
    for i in range(n+1):
        yield from combinations(range(n), i)


def single_error(table, M, ps, K):
    # With integral inverse-point-cap K, the extreme distributions are K-flats.
    return max(sum(prob * sum(abs(F(counts[y],K)-F(1,M)) for y in range(M))/2
                   for prob, counts in zip(ps,(Counter(table[s][x] for x in A)
                                              for s in range(len(ps)))))
               for A in combinations(range(len(table[0])),K))


def kernels(table, M, ps, K, r):
    N = len(table[0])
    eta = single_error(table,M,ps,K)
    a = min(F(M),1+M*eta)
    b = M-a
    vals = [[M*sum(p for p, row in zip(ps, table) if row[x]==row[y])
             for y in range(N)] for x in range(N)]
    sizes = [sum(q>a for q in row) for row in vals]
    assert max(sizes)<K
    # This test uses the strict boundary. Using >= here need not work.
    assert all(0<=q<=a+b*(q>a) for row in vals for q in row)
    d = a+b*min(1,F(K-1, 2**r))
    return vals, d, sizes, a


def check(pub, src, rr):
    n = len(rr)
    coeff = [kernels(*t,r) for t,r in zip(pub,rr)]
    for J in pref(n):
        sub = Counter()
        for x,p in src.items():
            sub[tuple(x[i] for i in J)] += p
        assert max(sub.values()) <= F(1, 2**sum(rr[i] for i in J))
        for x in src:
            probability = sum(p for y,p in src.items()
                if all(coeff[i][0][x[i]][y[i]] >
                 coeff[i][3]
                       for i in J))
            assert probability <= prod(min(1,F(pub[i][3]-1,2**rr[i])) for i in J)

    from_pairs = sum(px*py*prod(coeff[i][0][x[i]][y[i]] for i in range(n))
                     for x,px in src.items() for y,py in src.items())
    from_outputs = F(0)
    tv = F(0)
    M = prod(item[1] for item in pub)
    for s in product(*(range(len(obj[2])) for obj in pub)):
        weight = prod(obj[2][j] for obj,j in zip(pub,s))
        out = Counter()
        for x,p in src.items():
            out[tuple(obj[0][j][xx] for obj,j,xx in zip(pub,s,x))] += p
        from_outputs += weight*M*sum(p*p for p in out.values())
        tv += weight*(sum(abs(p-F(1,M)) for p in out.values())+(M-len(out))*F(1,M))/2
    assert from_pairs == from_outputs
    assert 4*tv*tv <= from_pairs-1 <= prod(k[1] for k in coeff)-1
    return tv


def main():
    caps = 0
    for rows in product(range(16),repeat=2):
        table = tuple(tuple((r>>x)&1 for x in range(4)) for r in rows)
        for K in (1,2,4):
            kernels(table,2,(F(1,3),F(2,3)),K,1)
            caps += 4

    rng = Random(20261127)
    heterogeneous = 0
    for j in range(18):
        para = ((4,2,2,1),(3,3,2,1),(4,1,4,0))
        pub = []
        for N,M,K,r in para:
            table = tuple(tuple(rng.randrange(M) for _ in range(N)) for _ in range(2))
            pub.append((table,M,(F(2,5),F(3,5)),K))
        weights = { (x,y,(x+y+j)%4): 1 for x in range(4) for y in range(3)}
        src = {x:F(p,12) for x,p in weights.items()}
        check(pub,src,(1,1,0))
        heterogeneous += 1

    # A correlated example where the tensor TV bound is strictly below one,
    # and the extractor genuinely fails the two-universal upper collision bound.
    table = [tuple((s & x).bit_count()%2 for x in range(8)) for s in range(8)]
    table.append((0,)*8)
    _, bound, _, _ = kernels(table,2,(F(1,9),)*9,4,2)
    assert bound**2 < 5 and F(1,2)<sum(F(1,9) for row in table if row[1]==row[2])
    source = {(x,y):F(1,32) for x in range(8) for y in range(8)
              if ((x ^ y) & 1)==0}
    assert check([(table,2,(F(1,9),)*9,4)]*2,source,(2,2)) < F(1,2)
    print(f"exact PASS: {caps} strong-extractor row caps, including nonuniform seeds")
    print(f"exact PASS: {heterogeneous+1} dense tensor identities and TV bounds, including a non-universal example")

    # Negative control isolates why the seed must occur in both reference laws.
    e = (((0,)*4, (1,)*4),2,(F(1,2),)*2,2)
    actual = check([e],{(i,):F(1,4) for i in range(4)},(1,))
    assert actual==F(1,2)
    marginal = Counter()
    for p,row in zip(e[2],e[0]):
        for y in row:
            marginal[y] += p/len(row)
    assert marginal == Counter({0:F(1,2),1:F(1,2)})
    print("exact PASS: public-seed versus uniform output-marginal control")


if __name__=="__main__":
    main()
