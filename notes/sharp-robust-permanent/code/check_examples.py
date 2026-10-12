#!/usr/bin/env python3
"""Exact-arithmetic spot checks for the robust permanent stability note.

These verify finite algebra and witnesses only, NOT the universal analytic
permanent inequality or the cited Bristiel--Caputo theorem.
"""
from fractions import Fraction
from itertools import permutations
from math import comb, factorial


def exponent_above_q(n: int, numerator: int, denominator: int) -> bool:
    """p=a/b>q_n iff (n!)**a > n**(n*b), tested over integers."""
    assert n >= 3 and numerator > denominator >= 1
    return factorial(n) ** numerator > n ** (n * denominator)


def cyclic_mass_at_identity(n: int, t: Fraction) -> Fraction:
    return (1 - t) / factorial(n) + t / n


def spike_violates(n: int, numerator: int, denominator: int,
                   t: Fraction) -> bool:
    """Strictly compare nu_t(id) with n^(-n/p), without floating-point."""
    a, b = numerator, denominator
    mass = cyclic_mass_at_identity(n, t)
    return mass.numerator ** a * n ** (n * b) > mass.denominator ** a


def check_distribution(n: int, t: Fraction) -> None:
    """Enumerate S_n and verify exact marginals and total variation."""
    assert 3 <= n <= 6 and 0 < t < 1
    group = {tuple((i + k) % n for i in range(n))
             for k in range(n)}
    assert len(group) == n
    group_all = list(permutations(range(n)))
    uniform = Fraction(1, factorial(n))
    prob = {pi: (1 - t) * uniform +
            (t / n if pi in group else 0) for pi in group_all}
    assert sum(prob.values()) == 1
    for i in range(n):
        for j in range(n):
            assert sum(w for pi, w in prob.items() if pi[i] == j) == Fraction(1, n)
    tv = sum((abs(prob[pi] - uniform) for pi in group_all), Fraction(0)) / 2
    assert tv == t * (1 - Fraction(n, factorial(n)))
    assert prob[tuple(range(n))] == cyclic_mass_at_identity(n, t)


def main() -> None:
    examples = ((3, 15, 8), (4, 7, 4), (6, 5, 3), (12, 3, 2))
    for n in range(3, 21):
        f = factorial(n)
        assert f < n ** (n - 1) and f * f > n ** n
        b = (1 + 2 * n) ** (n - 1) - 1
        subset_sum = sum(comb(n - 1, s - 1) * (2 * n) ** (s - 2)
                         for s in range(2, n + 1))
        assert 2 * n * subset_sum == b
    print("PASS: factorial threshold bounds and all subset identities, n=3,...,20")

    for n, a, b in examples:
        assert exponent_above_q(n, a, b)
        print(f"PASS: integer exponent comparison: n={n}, p={a}/{b}")

    for n, a, b, t in ((3, 15, 8, Fraction(1, 10)),
                       (4, 7, 4, Fraction(1, 100)),
                       (6, 5, 3, Fraction(1, 100))):
        check_distribution(n, t)
        assert spike_violates(n, a, b, t)
        assert cyclic_mass_at_identity(n, t) > Fraction(1, factorial(n))
        print(f"PASS: exact cyclic marginal/TV and violating spike: n={n}, t={t}")

    print("All exact finite checks passed; the all-n theorem remains analytic.")


if __name__ == "__main__":
    main()
