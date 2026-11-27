#!/usr/bin/env python3
"""Exact comparator enumeration; no determinant-moment argument."""
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt


def primes_up_to(n):
    return [p for p in range(2, n+1)
            if all(p % j for j in range(2, isqrt(p)+1))]


def rational_mass(points):
    candidates = {(F(0), F(y)) for x, y in points}
    for ((x, y), (u, v)) in combinations(points, 2):
        if u != x:
            a = F(v-y, u-x)
            candidates.add((a, y-a*x))
    return max(sum(w for (x, y), w in points.items() if a*x+b == y)
               for a, b in candidates)


def integer_mass(points, n, lower):
    # A larger nonnegative slope can only match points at x=0.
    return max(sum(w for (x, y), w in points.items() if a*x+b == y)
               for a in range(lower, n+2) for b in range(lower, n+1))


def modular_mass(points, p):
    # For each modular slope, tally the possible intercepts.
    best = 0
    for a in range(p):
        bins = {}
        for (x, y), w in points.items():
            b = (y-a*x) % p
            bins[b] = bins.get(b, 0)+w
        best = max(best, max(bins.values()))
    return best


def main():
    plist = primes_up_to(47)
    core = {(0, 2): 1, (2, 3): 1}
    assert all(integer_mass(core, 3, low) == 1 for low in (0, 1))
    assert rational_mass(core) == 2
    for p in plist:
        assert modular_mass(core, p) == (1 if p == 2 else 2)
    print(f'PASS core: both integer conventions, {len(plist)} prime optima, p=2 negative control')

    count = 0
    for n in range(1, 5):
        pset = [p for p in plist if p <= n*n+9]
        largest = {0: {p: F(0) for p in pset}, 1: {p: F(0) for p in pset}}
        for vals in product(range(-1, n+1), repeat=n+1):
            pt = {(x, y): 1 for x, y in enumerate(vals) if y >= 0}
            if not pt:
                continue
            base = [integer_mass(pt, n, lower) for lower in (0, 1)]
            a = rational_mass(pt)
            for p in pset:
                v = modular_mass(pt, p)
                assert all(v >= z for z in base)
                for low, z in enumerate(base):
                    largest[low][p] = max(largest[low][p], F(v-z, len(pt)))
                if p > n:
                    assert v >= a
                if p > n*n:
                    assert v == a
            count += 1
        for low in (0, 1):
            assert set(largest[low].values()) == {F(n, n+1) if low == 0 else F(1)}
    print(f'PASS graph enumeration: {count} deterministic partial graphs, sign/extrema and rational preservation')

    sharp = 0
    for n in range(2, 31):
        for p in primes_up_to(n*n):
            if p <= n:
                continue
            v = (p+n-1)//n
            u = n*v-p
            assert 1 <= u < n and 1 <= v <= n
            pt = {(0, 0): 1, (n, 1): 1, (u, v): 1}
            assert rational_mass(pt) == 2
            assert all((y-pow(n, -1, p)*x) % p == 0 for x, y in pt)
            sharp += 1
    print(f'PASS sharp cutoff: {sharp} prime/grid pairs with n<p<=n^2')


if __name__ == '__main__':
    main()
