#!/usr/bin/env python3
"""Exact integer/rational checks for the finite multiscale band choices.

This validates only the elementary parameter inequalities in the 010
multiscale deduction. It does not certify the imported analytic existence
theorems from OpenAI/math family 361.
"""

from fractions import Fraction
from math import isqrt

BETA = Fraction(4, 3)
A = Fraction(11, 10)
THETA = Fraction(7, 5)
# Rational upper surrogate for a^{-1} sqrt(C_*). The analytic construction
# permits this to be chosen arbitrarily close to 1.
RHO = Fraction(101, 100)
NUMBER_OF_BANDS = 5
K_MIN = 10_000


def floor_frac(x: Fraction) -> int:
    return x.numerator // x.denominator


def weighted_prefix(n: int) -> int:
    """Return sum_{l=1}^n (2l+1)(l+1), using integers only."""
    if n <= 0:
        return 0
    s1 = n * (n + 1) // 2
    s2 = n * (n + 1) * (2 * n + 1) // 6
    return 2 * s2 + 3 * s1 + n


def data_for(k: int, previous_M: int | None):
    L = isqrt(k)
    M = floor_frac(THETA * k)
    numerator = weighted_prefix(M) - weighted_prefix(L)
    denominator = (M + 1) ** 2 - (L + 1) ** 2
    D = floor_frac(BETA * (k + 1)) - 1
    tests = {
        "nonempty": M > L,
        "disjoint": previous_M is None or previous_M < L,
        "mean": RHO * numerator < k * denominator,
        "fixed_low": RHO * (L + 1) < k,
        "block_inside": floor_frac(BETA * (k + 1)) <= M,
        "dimension": Fraction((M + 1) ** 2, 1) > A * (D + 1) ** 2,
    }
    return L, M, D, numerator, denominator, tests


def choose_k(lower: int, previous_M: int | None):
    k = max(lower, K_MIN)
    if previous_M is not None:
        k = max(k, (previous_M + 1) ** 2)
    while True:
        data = data_for(k, previous_M)
        if all(data[-1].values()):
            return k, data
        k *= 2


def main() -> None:
    asymptotic = 2 * THETA * RHO / 3
    assert BETA > 1
    assert A >= 1
    assert A * BETA * BETA < THETA * THETA
    assert asymptotic < 1

    print("beta =", BETA)
    print("A =", A)
    print("theta =", THETA)
    print("theta^2 - A*beta^2 =", THETA * THETA - A * BETA * BETA)
    print("rho =", RHO)
    print("2*theta*rho/3 =", asymptotic)
    print("asymptotic slack =", 1 - asymptotic)
    print()
    print("r\tk\tL\tM\tD\tp\tcleared_mean_slack")

    previous_M = None
    lower = K_MIN
    for r in range(1, NUMBER_OF_BANDS + 1):
        k, data = choose_k(lower, previous_M)
        L, M, D, numerator, denominator, tests = data
        assert all(tests.values()), tests

        # Clear RHO's denominator from k*denominator-RHO*numerator.
        cleared_mean_slack = (
            k * denominator * RHO.denominator - RHO.numerator * numerator
        )
        assert cleared_mean_slack > 0

        p = (M + 1) ** 2
        print(f"{r}\t{k}\t{L}\t{M}\t{D}\t{p}\t{cleared_mean_slack}")

        previous_M = M
        lower = k + 1

    print()
    print("PASS: all exact quantitative multiscale band inequalities hold.")


if __name__ == "__main__":
    main()
