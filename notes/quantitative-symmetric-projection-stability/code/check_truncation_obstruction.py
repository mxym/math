#!/usr/bin/env python3
"""Exact facet-minor regression for the corner-truncation formula in paper.md.

These sixteen rational examples check the deficit identity and rate bound.
They do not verify the general distance lower bound against the equality class.
Only Python standard-library Fraction arithmetic is used; explicit exceptions
keep every check active under ``python3 -O``.
"""
from fractions import Fraction as F
from itertools import combinations
from math import factorial


def det(columns):
    n = len(columns)
    mat = [[F(columns[j][i]) for j in range(n)] for i in range(n)]
    result = F(1)
    for k in range(n):
        pivot = next((i for i in range(k, n) if mat[i][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            mat[k], mat[pivot] = mat[pivot], mat[k]
            result = -result
        value = mat[k][k]
        result *= value
        for i in range(k + 1, n):
            ratio = mat[i][k] / value
            for j in range(k + 1, n):
                mat[i][j] -= ratio * mat[k][j]
    return result


def verify(d, t):
    alpha = F(2 ** (d - 1)) - t ** (d - 1) / factorial(d - 1)
    gamma = t ** (d - 1) / factorial(d - 1)
    volume = F(2**d) - 2 * t**d / factorial(d)
    horizontal, lifted = [], []
    for i in range(d):
        for sign in (-1, 1):
            column = tuple(sign * alpha if k == i else F(0) for k in range(d))
            horizontal.append(column)
            lifted.append(column + (alpha,))
    for sign in (-1, 1):
        column = (sign * gamma,) * d
        horizontal.append(column)
        lifted.append(column + ((d - t) * gamma,))
    P = sum((abs(det(cols)) for cols in combinations(horizontal, d)), F(0))
    S = sum((abs(det(cols)) for cols in combinations(lifted, d + 1)), F(0))
    actual = F(1, 2) - S / (d * volume * P)
    c = F(1, 2) - F(1, 2 ** (d - 1))
    denominator = d * 2**d - 2 * t**d / factorial(d - 1)
    p = (2**d - 2 * t ** (d - 1) / factorial(d - 1)) / denominator
    expected = c * p * 2 * t**d / (factorial(d - 1) * 2**d + 2 * (d - 1) * t ** (d - 1))
    if actual != expected:
        raise ArithmeticError((d, t, actual, expected))
    if not 0 < actual <= c * t**d / (factorial(d) * 2 ** (d - 1)):
        raise ArithmeticError("Rate bound failed")
    return actual


if __name__ == "__main__":
    for d in (3, 4, 5, 6):
        for t in (F(1), F(1, 2), F(1, 3), F(1, 7)):
            print(f"d={d}, t={t}: deficit={verify(d,t)}; exact minors PASS")
    print("16 exact facet-minor cases verified independently.")
