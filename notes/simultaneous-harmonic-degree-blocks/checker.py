#!/usr/bin/env python3
"""Exact replay for the finite arithmetic in the simultaneous-block theorem.

This does NOT check the imported analytic existence theorem.
All arithmetic below uses fractions.Fraction.
"""

from fractions import Fraction
import argparse


def parse_fraction(s: str) -> Fraction:
    return Fraction(s)


def block_endpoint(beta: Fraction, k: int) -> int:
    x = beta * (k + 1)
    return x.numerator // x.denominator - 1


def check(beta: Fraction, A: Fraction, c: Fraction, k0: int, k1: int) -> None:
    assert beta > 1
    assert A > 1
    assert A * beta * beta < c
    assert c < Fraction(9, 4)

    margin = c - A * beta * beta
    print("beta =", beta)
    print("A =", A)
    print("c =", c)
    print("exact margin c - A*beta^2 =", margin)
    print("9/4 - c =", Fraction(9, 4) - c)

    total = 0
    for k in range(k0, k1 + 1):
        D = block_endpoint(beta, k)
        if D < k:
            continue
        lhs = c * (k + 1) ** 2
        rhs = A * (D + 1) ** 2
        assert lhs > rhs, (k, D, lhs, rhs)
        assert Fraction(D + 1, 1) <= beta * (k + 1)
        total += D - k + 1

    print(f"checked {total} integer degree instances for k={k0}..{k1}")
    print("PASS")


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--beta", default="7/5")
    p.add_argument("--A", default="11/10")
    p.add_argument("--c", default="11/5")
    p.add_argument("--k0", type=int, default=20)
    p.add_argument("--k1", type=int, default=200)
    args = p.parse_args()
    check(parse_fraction(args.beta), parse_fraction(args.A),
          parse_fraction(args.c), args.k0, args.k1)


if __name__ == "__main__":
    main()
