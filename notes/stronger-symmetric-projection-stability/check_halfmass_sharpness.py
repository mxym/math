#!/usr/bin/env python3
"""Exact finite regressions for halfmass.md; no hidden checkout or packages.

The mathematical statements in that note hold for every d >= 3. This program
directly enumerates unsigned direction types and sign-averages cofactors in
d = 3, 4, using Fraction arithmetic throughout. Checks survive python -O.
"""

from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial


def determinant(columns):
    n = len(columns)
    matrix = [[F(columns[j][i]) for j in range(n)] for i in range(n)]
    value = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if matrix[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            matrix[pivot], matrix[j] = matrix[j], matrix[pivot]
            value = -value
        entry = matrix[j][j]
        value *= entry
        for i in range(j + 1, n):
            ratio = matrix[i][j] / entry
            for k in range(j + 1, n):
                matrix[i][k] -= ratio * matrix[j][k]
    return value


@lru_cache(maxsize=None)
def sign_mean(magnitudes):
    return sum(
        abs(sum(s * c for s, c in zip(signs, magnitudes)))
        for signs in product((-1, 1), repeat=len(magnitudes))
    ) / F(2 ** len(magnitudes))


def require_equal(actual, expected, label):
    if actual != expected:
        raise RuntimeError(f"{label}: {actual} != {expected}")


def check_case(d, t):
    z = 24 - t ** 3
    p = (8 - t ** 2) / z
    r = (3 - t) * t ** 2 / z
    q = 1 / (3 - t)
    axes = [tuple(F(i == j) for i in range(d)) for j in range(d)]
    diagonal = tuple(q if i < 3 else F(0) for i in range(d))
    types = axes + [diagonal]
    probabilities = [F(3, d) * p] * 3 + [F(1, d)] * (d - 3)
    probabilities += [F(3, d) * r]
    require_equal(sum(probabilities), F(1), "law mass")

    a = F(0)
    for word in product(range(d + 1), repeat=d):
        mass = F(1)
        for i in word:
            mass *= probabilities[i]
        a += mass * abs(determinant([types[i] for i in word]))

    phi_mean = delta_mass = tail_mass = F(0)
    eta = t / (2 * (6 - t))
    for word in product(range(d + 1), repeat=d + 1):
        mass = F(1)
        for i in word:
            mass *= probabilities[i]
        columns = [types[i] for i in word]
        magnitudes = tuple(sorted(
            (abs(determinant(columns[:j] + columns[j + 1:]))
             for j in range(d + 1)), reverse=True
        ))
        total = sum(magnitudes)
        phi_mean += mass * magnitudes[3]
        delta_mass += mass * (total / 2 - sign_mean(magnitudes))
        if total:
            fourth = magnitudes[3] / total
            gap = F(1, 2) - magnitudes[0] / total
            if fourth > F(1, 7) and gap <= eta:
                tail_mass += mass * total

    v = sum(probabilities[i] * (sum(map(abs, types[i])) - 1)
            for i in range(d + 1))
    expected_a = F(27 * factorial(d), d ** d) * p ** 2 * (p + 3 * r * q)
    prefactor = F(81 * factorial(d + 1), d ** (d + 1))
    expected_phi = prefactor * p ** 3 * t ** 2 / z
    expected_delta = F(3, d) * t ** 3 * (8 - t ** 2) / (
        8 * z * (4 + t ** 2)
    )
    expected_tail = prefactor * p ** 3 * t ** 2 * (6 - t) / z
    expected_v = F(3, d) * t ** 3 / z
    require_equal(a, expected_a, "A")
    require_equal(phi_mean, expected_phi, "fourth cofactor")
    require_equal(delta_mass / ((d + 1) * a), expected_delta, "deficit")
    require_equal(tail_mass, expected_tail, "weighted half-mass tail")
    require_equal(v, expected_v, "support surplus")
    require_equal(v / expected_delta, 8 * (4 + t ** 2) / (8 - t ** 2),
                  "support surplus/deficit")
    if v > F(40, 7) * expected_delta:
        raise RuntimeError("support-surplus upper constant failed")


def main():
    cases = 0
    for d in (3, 4):
        for t in (F(1), F(1, 2), F(1, 5), F(1, 10)):
            check_case(d, t)
            cases += 1
    print(f"PASS {cases} exact cone-law cases: determinants, signs, tail, support")


if __name__ == "__main__":
    main()
