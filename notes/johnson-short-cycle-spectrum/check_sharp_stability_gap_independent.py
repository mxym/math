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


Q = [F(1, 2), F(1, 3), F(1, 4), F(1, 5), F(1, 6)]
FIXED = {1: F(-354), 3: F(-289)}
MAXIMUM = 43


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
    min_lower = None
    min_upper = None
    witness_lower = None
    witness_upper = None
    for moved in range(2,MAXIMUM+1):
        for shape in partitions(moved,moved):
            v = sum((w*(1-u(shape,q)) for w,q in zip(a,Q)),F(0))
            insist(F(9,14) <= v <= F(1),
                   f"exact second-checker dual violation at {shape}: {v}")
            if shape not in ((2,), (3,3)):
                sep = v-F(9,14)
                if min_lower is None or sep < min_lower:
                    min_lower, witness_lower = sep, shape
            if shape != (4,):
                sep = F(1)-v
                if min_upper is None or sep < min_upper:
                    min_upper, witness_upper = sep, shape
            if v == F(9,14):
                lows.append(shape)
            if v == 1:
                highs.append(shape)
            tested += 1
    insist(tested == 63260, "partition count mismatch")
    insist((2,) in lows and (3,3) in lows and (4,) in highs,
           "contacts were not attained")
    insist(min_lower == F(1877633,378000000)
           and witness_lower == (4,3), "sharp lower gap mismatch")
    insist(min_upper == F(11251048535763583,2116316160000000000)
           and witness_upper == (5,5,4), "sharp upper gap mismatch")
    insist(min_lower < min_upper, "incorrect worst gap")
    return tested, lows, highs, min_lower, min_upper


def verify_tail(a):
    s = sum((abs(w)*(q*q+(1-q)*(1-q))**22
             for w,q in zip(a,Q)),F(0))
    insist(s < F(7,50), "rational tail bound failed")
    insist(F(4,5)-F(7,50) > F(9,14)
           and F(4,5)+F(7,50) < 1, "incorrect tail interval")
    insist(F(33,50)-F(9,14) > F(1877633,378000000),
           "infinite lower-gap cutoff fails")
    insist(F(3,50) > F(1877633,378000000),
           "infinite upper-gap cutoff fails")
    return s


def main():
    a = coefficients()
    number, low, high, sharp_l, sharp_u = verify_finite(a)
    tail = verify_tail(a)
    print("EXACT RATIONAL COEFFICIENTS RECONSTRUCTED:",list(map(str,a)))
    print("INDEPENDENT FRACTION PARTITIONS REPLAYED:", number)
    print("LOWER CONTACT SHAPES:", low)
    print("UPPER CONTACT SHAPES:", high)
    print("INDEPENDENT SHARP LOWER GAP:",sharp_l,"shape",(4,3))
    print("INDEPENDENT SHARP UPPER GAP:",sharp_u,"shape",(5,5,4))
    print("TAIL < 7/50:", tail < F(7,50))
    print("INDEPENDENT SHARP STABILITY GAP CERTIFICATE PASSED")


if __name__ == "__main__":
    main()
