#!/usr/bin/env python3
"""Exact finite checks of q-permanent homogeneity, not counterexample search."""
import sys

# Fail closed: these verifiers require assertions to remain enabled.
if not __debug__:
    sys.stderr.write("ERROR: assertions are disabled. Run without -O/-OO and without PYTHONOPTIMIZE.\n")
    raise SystemExit(2)

from fractions import Fraction
from itertools import permutations
from math import lcm
from random import Random


def coefficients(a):
    n = len(a)
    out = [Fraction(0) for _ in range(n * (n - 1) // 2 + 1)]
    for p in permutations(range(n)):
        inv = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        term = Fraction(1)
        for i in range(n):
            term *= a[i][p[i]]
        out[inv] += term
    return out


def evaluate(c, q):
    return sum(c[k] * q**k for k in range(len(c)))


def derivative(c, q):
    return sum(k * c[k] * q**(k - 1) for k in range(1, len(c)))


def main():
    rng = Random(20261008)
    cases = 0
    for n in range(2, 7):
        for _ in range(6):
            v = [[Fraction(rng.randint(-4, 4), rng.randint(1, 7))
                  for _ in range(4)] for _ in range(n)]
            delta = Fraction(1, rng.randint(2, 9))
            b = [[sum(v[i][k] * v[j][k] for k in range(4))
                  + (delta if i == j else 0) for j in range(n)]
                 for i in range(n)]
            d = lcm(*(x.denominator for row in b for x in row))
            db = [[d * x for x in row] for row in b]
            assert d > 0 and all(x.denominator == 1 for row in db for x in row)
            c, scaled = coefficients(b), coefficients(db)
            assert scaled == [d**n * x for x in c]
            for q in [Fraction(1, 5), Fraction(2, 3), Fraction(9, 10), Fraction(1)]:
                assert evaluate(scaled, q) == d**n * evaluate(c, q)
                assert derivative(scaled, q) == d**n * derivative(c, q)
            cases += 1
    print(f'PASS: {cases} exact rational Gram-plus-diagonal matrices, orders 2..6.')
    print('PASS: integer denominator scaling of every q-permanent coefficient.')
    print('PASS: q-permanent and derivative homogeneity at four rational q values.')
    print('These checks test scaling only; no finite real counterexample is claimed.')


if __name__ == '__main__':
    main()
