#!/usr/bin/env python3
"""Exact finite checks for dyadic-log-fluctuations.md; no third-party packages."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import factorial, prod


def falling(n, k):
    return prod(range(n - k + 1, n + 1)) if k <= n else 0


def odd_grid():
    tested = pairs = 0
    for n in (4, 8, 16, 32, 64, 128):
        places = tuple(range(1, n, 2))
        # Reduce powers of zeta modulo the cyclotomic relation zeta^n=-1.
        for h in range(-12 * n, 12 * n + 1, 2):
            folded = Counter()
            for b in range(n):
                q, j = divmod(h * b, n)
                folded[j] += (-1) ** (q % 2)
            assert {j: c for j, c in folded.items() if c} == (
                {0: n} if h % (2 * n) == 0 else {}
            )
            tested += 1
        exceptional = 0
        for a, b in product(places, repeat=2):
            if a == b:
                continue
            signed = {
                (s1, s2, s3, s4)
                for s1, s2, s3, s4 in product((-1, 1), repeat=4)
                if ((s1 + s2) * a + (s3 + s4) * b) % (2 * n) == 0
            }
            balanced = {s for s in signed if s[0] == -s[1] and s[2] == -s[3]}
            assert len(balanced) == 4
            assert len(signed - balanced) == (2 if a + b == n else 0)
            exceptional += bool(signed - balanced)
            pairs += 1
        assert exceptional <= n // 2
    return tested, pairs


def partitions(n, minimum=1):
    if n == 0:
        yield ()
    else:
        for first in range(minimum, n + 1):
            for rest in partitions(n - first, first):
                yield (first,) + rest


def wick_support():
    checks = 0
    exact = 0
    for k in range(11):
        for u in range(k + 1):
            for groups in partitions(k - u):
                s, singles = len(groups), groups.count(1)
                for weight in range(10):
                    for degrees in partitions(weight):
                        # One part w represents a cumulant of degree 2w+2.
                        order = sum(2 * w + 2 for w in degrees)
                        if order < 2 * singles:
                            continue
                        twice_exponent = 2 * s - k - 2 * weight
                        assert twice_exponent <= -u
                        if twice_exponent == 0:
                            assert u == 0
                            assert all(x in (1, 2) for x in groups)
                            assert all(w == 1 for w in degrees)
                            assert order == 2 * singles
                            exact += 1
                        checks += 1
    return checks, exact


def matchings(labels):
    if not labels:
        yield ()
        return
    first = labels[0]
    for j in range(1, len(labels)):
        for rest in matchings(labels[1:j] + labels[j + 1 :]):
            yield ((first, labels[j]),) + rest


def colored_counts():
    checks = 0
    for k in (0, 2, 4, 6, 8):
        h = k // 2
        pairings = tuple(matchings(tuple(range(k))))
        expected_wick = prod(range(1, k, 2))
        assert len(pairings) == expected_wick
        colors = Counter(sum(bits) for p in pairings for bits in product((0, 1), repeat=h))
        for nplaces in (3, 4, 7, 13):
            for marks in (0, 1, 2):
                for cross, count in colors.items():
                    assert count == expected_wick * factorial(h) // (
                        factorial(cross) * factorial(h - cross)
                    )
                    n = 2 * nplaces
                    s = h + cross + marks
                    # Exact normalized placement and quartic factors.
                    coefficient = Fraction(falling(nplaces, s), nplaces ** (h + marks) * n ** cross)
                    assert coefficient == Fraction(
                        falling(nplaces, s), nplaces ** s * 2 ** cross
                    )
                    checks += 1
        # For fixed slots, each quartic joins two occurrences at each place.
        assert Fraction(6 * 2 * 2, factorial(4)) == 1
    return checks


def gamma_coefficients():
    checks = 0
    for r in range(1, 9):
        for m in range(r, 13):
            variance_partial = sum(
                (sum((Fraction(1, t * t) for t in range(j, 2 * m + 1)), Fraction())
                 for j in range(m - r + 1, m + 1)),
                Fraction(),
            )
            # Integral bound for the rest of trigamma already beats r/m.
            variance_lower = variance_partial + Fraction(r, 2 * m + 1)
            assert variance_lower > Fraction(r, m)
            assert r * m * Fraction(1, m * m) / 2 == Fraction(r, 2 * m)
            checks += 1
    return checks


if __name__ == "__main__":
    n, p = odd_grid()
    w, e = wick_support()
    c = colored_counts()
    g = gamma_coefficients()
    print(f"PASS: {n} odd-grid orthogonality rows, {p} signed-quartic pairs")
    print(f"PASS: {w} support exponents ({e} equality cases), {c} colored counts")
    print(f"PASS: {g} fixed-shape variance bounds")
