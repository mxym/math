#!/usr/bin/env python3
"""Verify a fixed eight-prime arithmetic progression and both pairings."""
from itertools import combinations
from math import gcd, isqrt, prod

P = tuple(199+210*i for i in range(8))
assert all(p>2 and all(p%d for d in range(2,isqrt(p)+1)) for p in P)
M = ((0,5),(1,2),(3,6),(4,7))
N = ((0,3),(1,4),(2,7),(5,6))
assert set(M).isdisjoint(N)

def values(matching):
    assert sorted(v for e in matching for v in e) == list(range(8))
    a = tuple(sorted(P[i]*P[j] for i,j in matching))
    assert all(gcd(u,v)==1 for u,v in combinations(a,2))
    return a

A,B = values(M),values(N)
assert A == (248551,253171,1209511,1734091)
assert B == (164971,424951,1033111,1822291)
assert set(A).isdisjoint(B)
assert prod(A)==prod(B)==prod(P)==131980928240562546234721
assert sum(A)==sum(B)==3445324
assert sum(x*x for x in A)==sum(x*x for x in B)==4595861610244
assert sum(x**3 for x in A)!=sum(x**3 for x in B)
print("PASS: 8 fixed primes, two edge-disjoint pairings, common product and moments 1 and 2")
