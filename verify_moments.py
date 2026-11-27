#!/usr/bin/env python3
"""Enumerate square matrices and count their kernel events directly."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, prod


def binary():
    for r in range(1, 5):
        v = 2**r
        D = I = 0
        for x, y, z in combinations(range(1, v), 3):
            if x ^ y ^ z == 0:
                D += 1
            else:
                I += 1
        assert D == (v - 1) * (v - 2) // 6
        assert I == (v - 1) * (v - 2) * (v - 4) // 6
        n = success = partial = 0
        sums = [0, 0, 0]
        for cols in product(range(v), repeat=r):
            image = [0]
            for a in cols:
                image += [b ^ a for b in image]
            killed = image.count(0) - 1
            exact = int(killed == 0)
            trunc = 1 - killed + comb(killed, 2) - comb(killed, 3)
            assert trunc <= exact
            success += exact
            partial += trunc
            n += 1
            for j in range(1, 4):
                sums[j-1] += comb(killed, j)
        assert tuple(F(s, n) for s in sums) == (
            F(v-1, v), F(comb(v-1, 2), v**2), F(D, v**2) + F(I, v**3))
        B = F(1, v) + F((v-1)*(v-2)*(v+4), 6*v**3)
        assert F(partial, n) == B == F(1, 6) + F(7*v*v-10*v+8, 6*v**3)
        assert F(success, n) == prod(1 - F(1, 2**j) for j in range(1, r+1))
        assert F(success, n) >= B >= F(1, 6)
        print(f"binary r={r} matrices={n} dep3={D} indep3={I} "
              f"success={F(success, n)} trunc={B}")
    for r in range(1, 81):
        v = 2**r
        assert 7*v*v - 10*v + 8 > 0
        assert 6*sum(comb(v-1, j) for j in range(1, 4)) < v**3


def ternary():
    q = 3
    for r in (1, 2, 3):
        vectors = list(product(range(q), repeat=r))
        lines = [x for x in vectors if next((a for a in x if a), 0) == 1]
        assert len(lines) == (q**r - 1) // (q - 1)
        success = killed_sum = 0
        for rows in product(vectors, repeat=r):
            killed = sum(all(sum(a*b for a, b in zip(row, x)) % q == 0
                             for row in rows) for x in lines)
            success += killed == 0
            killed_sum += killed
        n = q**(r*r)
        assert F(killed_sum, n) == F(len(lines), q**r)
        assert F(success, n) >= 1 - F(killed_sum, n)
        assert F(success, n) == prod(1 - F(1, q**j) for j in range(1, r+1))
        assert len(lines)*(F(1, q**r) + F(1, 24*q**r)) < F(25, 48)
        print(f"ternary r={r} matrices={n} lines={len(lines)} success={F(success, n)}")


if __name__ == "__main__":
    binary()
    ternary()
    print("moments PASS")
