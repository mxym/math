#!/usr/bin/env python3
"""Finite rational checks for the sharp atom-TV construction (paper, section 8).

This checks a construction, not the general analytic inequality.
"""
from fractions import Fraction
from itertools import permutations
from math import comb, factorial

for n in (3, 4, 5, 6):
    items = list(permutations(range(n)))
    identity = tuple(range(n))
    derangements = [p for p in items if all(p[i] != i for i in range(n))]
    transpositions = [p for p in items if sum(p[i] != i for i in range(n)) == 2]
    assert len(transpositions) == comb(n, 2)
    D, T = set(derangements), set(transpositions)
    assert not D.intersection(T)
    b = Fraction(n - 2, n)
    P = {p: (b if p == identity else Fraction(0)) +
         (Fraction(2, n * len(D)) if p in D else Fraction(0)) for p in items}
    Q = {p: Fraction(1, len(T)) if p in T else Fraction(0) for p in items}
    assert sum(P.values()) == sum(Q.values()) == 1
    for i in range(n):
        for j in range(n):
            assert sum(P[p] for p in items if p[i] == j) == sum(
                Q[p] for p in items if p[i] == j)
    t, u = Fraction(1, 1000), Fraction(1, factorial(n))
    mu = {p: u + t * (P[p] - Q[p]) for p in items}
    assert min(mu.values()) >= 0
    assert sum(mu.values()) == 1
    assert sum(abs(mu[p] - u) for p in items) / 2 == t
    assert mu[identity] == u + b * t
    assert all(sum(mu[p] for p in items if p[i] == j) == Fraction(1, n)
               for i in range(n) for j in range(n))
    print("PASS: n=%s, TV=%s, atom-excess=%s" % (n, t, b * t))
print("Rational finite witnesses passed; see paper for all-n proof.")
