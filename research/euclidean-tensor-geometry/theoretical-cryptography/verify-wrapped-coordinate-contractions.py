#!/usr/bin/env python3
"""Finite checks for wrapped coordinate contractions (Python 3 standard library)."""
from fractions import Fraction as F
from itertools import combinations, product
from math import cos, exp, log, pi, sqrt
from random import Random


def distance(a, b, q):
    d = abs(a-b)
    return min(d, q-d)


def is_contraction(a, b, q):
    return all(distance(b[i], b[j], q) <= distance(a[i], a[j], q)
               for i, j in combinations(range(len(a)), 2))


def arc_mask(a, r, q):
    # Arc endpoints are in the integer q-grid. Each open grid cell is fully
    # contained or fully outside; use the midpoint in doubled coordinates.
    return sum(1 << j for j in range(q) if distance(2*a, 2*j+1, 2*q) < 2*r)


def union_count(places, radii, q):
    seen = 0
    for a, r in zip(places, radii):
        seen |= arc_mask(a, r, q)
    return seen.bit_count()


def check_arcs():
    q = 8
    count = strict = 0
    sites = [(0, *x) for x in product(range(q), repeat=2)]
    for a, b in product(sites, repeat=2):
        if not is_contraction(a, b, q):
            continue
        for radii in product(range(q//2+1), repeat=3):
            a_len = union_count(a, radii, q)
            b_len = union_count(b, radii, q)
            assert b_len <= a_len
            count += 1
            strict += b_len < a_len
    rng = Random(11621)
    q = 36
    bigger = 0
    for j in range(22000):
        n = rng.randint(2, 8)
        a = [rng.randrange(q) for _ in range(n)]
        b = [rng.randrange(q) for _ in range(n)]
        radii = [rng.randrange(q//2+1) for _ in range(n)]
        if j % 4 == 0:
            # Reflect a freely chosen segment across the 0--q/2 axis:
            # applying the fold to all labels is a circle contraction.
            b = [a_i if a_i <= q//2 else q-a_i for a_i in a]
            assert is_contraction(a, b, q)
        if is_contraction(a, b, q):
            a_len = union_count(a, radii, q)
            b_len = union_count(b, radii, q)
            assert b_len <= a_len
            bigger += 1
    assert strict > 0
    print(f"PASS {count} exhaustive exact arc inequalities ({strict} strict)"
          f" and {bigger} larger sampled contractions")


def compositions(total, n):
    if n == 1:
        yield (total,)
    else:
        for x in range(total+1):
            for tail in compositions(total-x, n-1):
                yield (x, *tail)


def check_gap_maxima():
    # F(g)=g(2q-g) is a strictly concave test objective on g in [0,q].
    # All calculations use exact rational arithmetic.
    q = 24
    count = attained = 0
    for n in (2, 3, 4, 5, 6):
        best_by_maxgap = [-1]*(q+1)
        for g in compositions(q, n):
            mx = max(g)
            score = 2*q*q-sum(x*x for x in g)
            best_by_maxgap[mx] = max(best_by_maxgap[mx], score)
        for arc in range(q+1):
            l0 = min(F(arc), F(q*(n-1), n))
            rest = l0/(n-1)
            bound = 2*q*q-(q-l0)**2-(n-1)*rest**2
            actual = max(best_by_maxgap[q-arc:])
            assert actual <= bound
            if rest.denominator == 1 and l0.denominator == 1:
                assert actual == bound
                attained += 1
            count += 1
    print(f"PASS {count} discrete-gap sharp upper bounds ({attained} attained on grid)")


def arctan_enclosure(z, count=12):
    # Alternating arctan power series for |z|<1.
    res = sum((-1)**j * z**(2*j+1)/(2*j+1) for j in range(count))
    nxt = res + (-1)**count * z**(2*count+1)/(2*count+1)
    return min(res, nxt), max(res, nxt)


def check_exact_reversal():
    # Machin's identity pi=16 atan(1/5)-4 atan(1/239).
    a1, a2 = arctan_enclosure(F(1, 5))
    b1, b2 = arctan_enclosure(F(1, 239))
    lo, hi = 16*a1-4*b2, 16*a2-4*b1
    assert lo*lo > F(986, 100) and hi*hi < 10
    assert F(2450, 1000)**2 > 6 and F(1414, 1000)**2 < 2
    bound = F(2, 9)-F(10, 2187) - 2*(F(2450, 1000)-F(1414, 1000))/F(986, 100)
    assert bound > F(7, 1000)
    assert F(1, 81) < F(1, 72)
    # Show the displayed remainder bound simultaneously for all rho<=1/1000,
    # after dividing by rho^2 or rho^4 as appropriate.
    rho = F(1, 1000)
    assert 2/(1-rho**5) < 3
    assert 4+6*(1+2*rho)*rho**2+9*rho**6 < 5
    assert 2*bound-10*rho > 0
    print(f"PASS exact limiting-coefficient gap >= {bound} and positive finite-width gap")


def numerical_tv(s, shift, q=512):
    def line(delta):
        return [1+2*sum(exp(-pi*s*s*k*k)*cos(2*pi*k*((j+0.5)/q-delta))
                       for k in range(1, 101)) for j in range(q)]
    a = line(0)
    bx, by = line(shift[0]), line(shift[1])
    return sum(abs(x*y-u*v) for x, u in zip(a, bx)
               for y, v in zip(a, by))/(2*q*q)


def illustrate():
    a, b = (1/12, 1/12), (1/9, 0)
    regimes = ((0.06, -1), (sqrt(log(1000)/pi), 1))
    for s, expected in regimes:
        x, y = numerical_tv(s, a), numerical_tv(s, b)
        assert expected*(y-x) > 0
        print(f"PASS numerical illustration s={s:.6g}: diagonal={x:.12g}, axis={y:.12g}")


if __name__ == "__main__":
    check_arcs()
    check_gap_maxima()
    check_exact_reversal()
    illustrate()
