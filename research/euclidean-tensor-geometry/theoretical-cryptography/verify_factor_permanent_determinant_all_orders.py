#!/usr/bin/env python3
"""Exact scalar checks for FactorPermanentDeterminantAllOrders.md."""

from fractions import Fraction as F
from math import factorial, isqrt


def require(condition, description):
    if not condition:
        raise ArithmeticError(description)


Q = 10**6


def lower_sqrt(q):
    return F(isqrt(Q * Q * q.numerator // q.denominator), Q)


def upper_sqrt(q):
    return lower_sqrt(q) + F(1, Q)


def main():
    print("n  t   floor(10^6 L)  floor(10^6 R)")
    for n in range(5, 16):
        m = n // 2
        ell = n - m
        t = F(2, 5) if n == 5 else F(1, 5) if n == 15 else F(3, 10)
        rho_sq = F(factorial(n)**2, n**n)
        rho_l, rho_u = lower_sqrt(rho_sq), upper_sqrt(rho_sq)
        delta = upper_sqrt((1 - t)**(n - 1) * (1 + (n - 1) * t))
        alpha = upper_sqrt(F(n, 2 * (n - 1))**m)
        k = F(factorial(m) + factorial(ell) - 2, 2)
        left = (rho_l - 1) * (1 - delta) - k * t**2
        right = 1 - alpha - (1 - 1/rho_u) * delta / (1 - t**2)
        require(1 < rho_l < rho_u and delta < 1 and left > 0 and right > 0,
                ("finite splice", n, left, right))
        print(n, t, (Q * left).__floor__(), (Q * right).__floor__())

    # Rational comparisons in the uniform n >= 16 argument.
    require(F(224, 269) < F(11, 12)**2, "large tail: determinant")
    require(F(11, 12) * F(400, 399) < 1 - F(8, 15)**4,
            "large tail: attenuation")
    require(F(3, 4)**2 * F(16, 15) < F(4, 5)**2, "cycle cutoff")
    require((54 * F(15, 128)) > F(25, 4), "small tail: slope")
    require(F(7, 4) < F(4, 3)**2, "small tail: square root")
    require(F(factorial(16), 16**8) - 1 > 54, "rho base")
    print("PASS: eleven strict scalar splices and six uniform comparisons")


if __name__ == "__main__":
    main()
