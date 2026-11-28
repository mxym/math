#!/usr/bin/env python3
"""Dependency-free exact checks for the one-sum squarefree-three-prime theorem."""

from itertools import combinations
from math import factorial, prod

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)


def det_bareiss(matrix):
    a = [row[:] for row in matrix]
    n = len(a)
    if n == 0:
        return 1
    sign = 1
    previous = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
        previous = pivot
        for i in range(k + 1, n):
            a[i][k] = 0
    return sign * a[-1][-1]


def resultant_value(t, c, n, j):
    f = [1, -t, t + c, -n]
    g = [1] * (j + 1)
    size = j + 3
    sylvester = []
    for shift in range(j):
        sylvester.append([0] * shift + f + [0] * (size - shift - 4))
    for shift in range(3):
        sylvester.append([0] * shift + g + [0] * (size - shift - j - 1))
    return det_bareiss(sylvester)


def sigma_prime_power(p, j):
    return (p ** (j + 1) - 1) // (p - 1)


def finite_difference(values, order):
    row = values[:]
    for _ in range(order):
        row = [row[i + 1] - row[i] for i in range(len(row) - 1)]
    return row[0]


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


triples = 0
resultant_cases = 0
normalization_cases = 0

for triple in combinations(PRIMES, 3):
    p, q, r = triple
    n = p * q * r
    phi = (p - 1) * (q - 1) * (r - 1)
    c = n - phi - 1
    s = p + q + r

    roots = []
    for x in range(2, s + 1):
        value = x**3 - s * x**2 + (s + c) * x - n
        if value == 0 and is_prime(x):
            roots.append(x)
    assert tuple(roots) == triple

    m = (n - 1).bit_length()
    j_norm = 16 * m
    sigma_norm = prod(sigma_prime_power(x, j_norm) for x in triple)
    assert n ** (j_norm + 1) // sigma_norm == phi
    normalization_cases += 1

    for j in range(2, 7):
        sigma = prod(sigma_prime_power(x, j) for x in triple)
        assert resultant_value(s, c, n, j) == sigma
        values = [resultant_value(t, c, n, j) - sigma for t in range(j + 1)]
        top_difference = finite_difference(values, j)
        assert top_difference % factorial(j) == 0
        assert top_difference // factorial(j) == j + 1
        resultant_cases += 1

    triples += 1

print("PASS")
print(f"prime triples: {triples}")
print(f"exact resultant/leading-coefficient cases: {resultant_cases}")
print(f"high-power totient-floor cases: {normalization_cases}")
