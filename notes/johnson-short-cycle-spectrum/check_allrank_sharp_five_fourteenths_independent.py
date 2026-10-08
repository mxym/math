#!/usr/bin/env python3
"""Independent standard-library replay of the universal Johnson 5/14 dual.

Unlike check_allrank_sharp_five_fourteenths.py, this script reconstructs
three coefficients from exact rational contact equations instead of accepting
the five final coefficients; it uses a separate recursive partition generator
and Fraction-valued products rather than cleared-denominator integer products.
It is independently specified and self-contained (no imports from other
project modules, no floating point, optimizer, or assertion-only tests).
"""
from fractions import Fraction as F


Q = [F(1, 2), F(3, 8), F(1, 4), F(1, 5), F(1, 6)]
FIXED = {1: F(-344827, 1000), 3: F(-205889, 1000)}
MAXIMUM = 41


def insist(cond, detail):
    if not cond:
        raise ArithmeticError(detail)


def u(cycles, q):
    result = F(1)
    for ell in cycles:
        result *= q ** ell + (1-q) ** ell
    return result


def solve(A, b):
    mat = [[F(x) for x in row] + [F(y)]
           for row, y in zip(A, b)]
    n = len(b)
    insist(len(A) == n and all(len(x) == n+1 for x in mat),
           "bad rational matrix")
    for j in range(n):
        pivot = next((i for i in range(j, n) if mat[i][j]), None)
        insist(pivot is not None, "singular contacts")
        mat[j], mat[pivot] = mat[pivot], mat[j]
        mul = mat[j][j]
        mat[j] = [v / mul for v in mat[j]]
        for i in range(n):
            if i == j:
                continue
            coeff = mat[i][j]
            mat[i] = [mat[i][h] - coeff * mat[j][h]
                      for h in range(n+1)]
    return [mat[i][-1] for i in range(n)]


def coefficients():
    missing = [i for i in range(5) if i not in FIXED]
    contacts = [((2,), F(9,14)), ((4,), F(1)), ((), F(4,5))]
    matrix = []
    targets = []
    for cycles, target in contacts:
        def moment(i):
            return F(1) if not cycles else 1-u(cycles, Q[i])
        matrix.append([moment(i) for i in missing])
        targets.append(target-sum((FIXED[i]*moment(i) for i in FIXED), F(0)))
    unknowns = solve(matrix, targets)
    a = [FIXED[i] if i in FIXED else unknowns[missing.index(i)]
         for i in range(5)]
    insist(sum(a) == F(4, 5), "inconsistent sum")
    for cycles, val in [((2,), F(9,14)), ((4,), F(1)),
                        ((3,3), F(9,14))]:
        insist(sum((w*(1-u(cycles, q)) for w,q in zip(a,Q)),F(0)) == val,
               f"bad contact: {cycles}")
    return a


def partitions(n, largest):
    """Unique nonincreasing partitions into parts at least 2."""
    if n == 0:
        yield ()
    else:
        for first in range(min(n,largest),1,-1):
            for rest in partitions(n-first, first):
                yield (first,)+rest


def verify_finite(a):
    tested = 0
    lows = []
    highs = []
    for moved in range(2,MAXIMUM+1):
        for shape in partitions(moved,moved):
            v = sum((w*(1-u(shape,q)) for w,q in zip(a,Q)),F(0))
            insist(F(9,14) <= v <= F(1),
                   f"exact second-checker dual violation at {shape}: {v}")
            if v == F(9,14):
                lows.append(shape)
            if v == 1:
                highs.append(shape)
            tested += 1
    insist(tested == 44582, "partition count mismatch")
    insist((2,) in lows and (3,3) in lows and (4,) in highs,
           "contacts were not attained")
    return tested, lows, highs


def verify_tail(a):
    s = sum((abs(w)*(q*q+(1-q)*(1-q))**21
             for w,q in zip(a,Q)),F(0))
    insist(s < F(7,50), "rational tail bound failed")
    insist(F(4,5)-F(7,50) > F(9,14)
           and F(4,5)+F(7,50) < 1, "incorrect tail interval")
    return s


def main():
    a = coefficients()
    number, low, high = verify_finite(a)
    tail = verify_tail(a)
    print("EXACT RATIONAL COEFFICIENTS RECONSTRUCTED:",list(map(str,a)))
    print("INDEPENDENT FRACTION PARTITIONS REPLAYED:", number)
    print("LOWER CONTACT SHAPES:", low)
    print("UPPER CONTACT SHAPES:", high)
    print("TAIL < 7/50:", tail < F(7,50))
    print("INDEPENDENT UNIVERSAL 5/14 CHECKER PASSED")


if __name__ == "__main__":
    main()
