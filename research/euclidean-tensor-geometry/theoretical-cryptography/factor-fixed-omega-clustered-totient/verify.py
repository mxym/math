#!/usr/bin/env python3
"""Exact checks for two-point coefficient recovery; standard library only."""

from fractions import Fraction
from itertools import combinations
from math import comb


def primes_upto(n):
    out = []
    for x in range(2, n + 1):
        if all(x % p for p in out if p * p <= x):
            out.append(x)
    return out


def iroot(n, k):
    lo, hi = 0, n + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    return lo


def esym(values, j):
    if j == 0:
        return 1
    ans = 0
    for idx in combinations(range(len(values)), j):
        term = 1
        for i in idx:
            term *= values[i]
        ans += term
    return ans


def require(ok, msg):
    if not ok:
        raise AssertionError(msg)


primes = primes_upto(31)[:11]
checked = 0
for k in range(3, 8):
    for ps in combinations(primes, k):
        n = 1
        tot = 1
        for p in ps:
            n *= p
            tot *= p - 1

        v = iroot(n, k)
        require(v**k <= n < (v + 1)**k, "integer root")
        require(ps[0] <= v <= ps[-1], "anchor location")

        shifted = [p - v for p in ps]
        h = ps[-1] - ps[0]
        c = [esym(shifted, j) for j in range(k + 1)]
        require(c[0] == 1, "monic")

        prefix = [1]
        for j in range(1, k - 1):
            def S(t, value):
                known = sum(prefix[q] * t ** (k - q)
                            for q in range(j))
                return Fraction(value - known, t ** (k - j - 1))

            center = S(v, n) - S(v - 1, tot)
            bound = sum(
                Fraction(comb(k, j + s) * (s - 1) * h ** (j + s),
                         (v - 1) ** s)
                for s in range(2, k - j + 1)
            )
            require(abs(Fraction(c[j]) - center) <= bound,
                    "tail bound")
            prefix.append(c[j])

        aa = n - sum(c[q] * v ** (k - q) for q in range(k - 1))
        bb = tot - sum(c[q] * (v - 1) ** (k - q)
                       for q in range(k - 1))
        recovered_km1 = aa - bb
        recovered_k = aa - v * recovered_km1
        require(recovered_km1 == c[k - 1], "coefficient k-1")
        require(recovered_k == c[k], "coefficient k")

        for p in ps:
            root = v - p
            require(sum(c[j] * root ** (k - j)
                        for j in range(k + 1)) == 0,
                    "shifted integer root")
        checked += 1

require(checked == 1749, "coverage")
print("fixed-omega clustered totient checker")
print(f"tuples_checked = {checked}")
print("k_range = 3..7")
print("finite_difference_centers = PASS")
print("exact_tail_bounds = PASS")
print("last_two_coefficients = PASS")
print("integer_root_recovery = PASS")
print("standard_library_only = PASS")
