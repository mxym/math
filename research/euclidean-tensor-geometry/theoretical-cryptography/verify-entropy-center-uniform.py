#!/usr/bin/env python3
"""Exact rational arithmetic behind the entropy-center precision bounds."""
from fractions import Fraction as F
from itertools import product
from math import factorial, isqrt


def exp_tail_lower(x, cutoff):
    return sum(x**j / factorial(j) for j in range(cutoff+1))


def bound_constants():
    assert exp_tail_lower(F(3), 8) > 20
    assert exp_tail_lower(F(25, 8), 8) > F(45, 2)
    assert exp_tail_lower(F(2), 2) == 5
    assert exp_tail_lower(F(2), 3) > 5
    rank_one_energy = 6*F(1, 20)*(1+F(1, 20))/(1-F(1, 20))**3
    assert rank_one_energy+F(6, 19) < 1
    assert 20*F(4, 2**16)/(1-F(4, 2**16)) < F(1, 4)
    assert F(40, 2**20-1) < F(1, 4)
    x, q = F(25, 8), F(2, 45)
    h = 6*x/(1/q+6)+18*x*q**3+144*x*q**4/(1-F(25, 16)*q)
    assert h == F(3427063, 5155650) < F(2, 3)
    assert 2*x/(1/q-1)+F(2, 3) == F(247, 258) < 1
    assert x*2 == F(25, 4)
    return h


def check_hex_shells():
    # Q>=3/4*max(m^2,n^2), so this box contains all vectors through K.
    K = 100
    M = isqrt(4*K//3)+1
    counts = [0]*(K+1)
    for m, n in product(range(-M, M+1), repeat=2):
        q = m*m+n*n+m*n
        if q <= K:
            counts[q] += 1
    assert counts[:4] == [1, 6, 0, 6]
    assert all(counts[k] <= 9*k for k in range(1, K+1))
    return K+1


def quadratic(v, c, m, n):
    return m*m+v*n*n+2*c*m*n


def check_shape_region():
    # pi>3, so det^2 <=36/25 at shortest length 1 is a rational
    # sufficient subregion of the theorem's det <=2*pi/5.
    count = 0
    for i, j in product(range(21), repeat=2):
        v, c = 1+F(i, 40), F(j, 40)
        detsq = v-c*c
        if detsq > F(36, 25):
            continue
        assert detsq > 0
        for m, n in product(range(-3, 4), repeat=2):
            if not (m or n):
                continue
            assert quadratic(v, c, m, n) >= m*m+n*n-abs(m*n) >= 1
        # Rotation/det of the primal has squared shortest 1/detsq.
        # 9/detsq lower-bounds the product of the two precision coordinates.
        assert 9/detsq >= F(25, 4)
        count += 1
    v, c = F(1), F(1, 4)
    assert v-c*c == F(15, 16)
    minima = {(m, n) for m, n in product(range(-2, 3), repeat=2)
              if quadratic(v, c, m, n) == 1}
    assert minima == {(1, 0), (-1, 0), (0, 1), (0, -1)}
    assert c != 0  # Two nonorthogonal shortest directions rule out a rectangle.
    return count


if __name__ == "__main__":
    c = bound_constants()
    s = check_hex_shells()
    f = check_shape_region()
    print(f"PASS: exact hexagonal energy bound {c}; {s} shell counts, "
          f"{f} rational shape checks and a strictly nonorthogonal example")
