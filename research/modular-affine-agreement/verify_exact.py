"""Exact finite regression with line construction from point pairs."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product


def scores(points, p):
    # Each point key occurs once; use integer weights throughout.
    total = sum(points.values())
    graphs = {(Fraction(0), Fraction(y)) for x, y in points}
    for (x, y), (u, v) in combinations(points, 2):
        if x != u:
            slope = Fraction(v - y, u - x)
            graphs.add((slope, y - slope * x))
    rational = signed = natural = positive = 0
    for slope, offset in graphs:
        w = sum(weight for (x, y), weight in points.items()
                if y == slope * x + offset)
        rational = max(rational, w)
        if slope.denominator == offset.denominator == 1:
            signed = max(signed, w)
            if slope >= 0 and offset >= 0:
                natural = max(natural, w)
    # A singleton on a positive-integer line is possible exactly when y>x.
    positive = max([0] + [w for (x, y), w in points.items() if y > x])
    for slope, offset in graphs:
        if slope.denominator == offset.denominator == 1 and slope > 0 and offset > 0:
            positive = max(positive, sum(w for (x, y), w in points.items()
                                        if y == slope * x + offset))
    best_field = 0
    for a in range(p):
        hist = Counter()
        for (x, y), w in points.items():
            hist[(y - a * x) % p] += w
        best_field = max(best_field, max(hist.values()))
    return tuple(Fraction(w, total) for w in
                 (natural, signed, rational, best_field, positive))


def determinants(points):
    (x, y), (u, v), (z, t) = points
    return (u - x) * (t - y) - (z - x) * (v - y)


def prime_budget(M, ps):
    return max(sum(d % p == 0 for p in ps) for d in range(1, M + 1))


def witness_totals(points, primes):
    total = sum(points.values())
    nr = Counter()
    for ((x, y), a), ((u, v), b), ((s, t), c) in product(points.items(), repeat=3):
        if x == u and y == v:
            continue
        d = determinants(((x, y), (u, v), (s, t)))
        for p in primes:
            coll = (x-u) % p == (y-v) % p == 0
            rankdrop = d != 0 and d % p == 0
            if coll or rankdrop:
                nr[p] += a * b * c
    return {p: Fraction(nr[p], total**3) for p in primes}


def exhaustive():
    ps = (2, 3, 5, 7, 11, 17, 19)
    for n in range(1, 5):
        checked = 0
        max_nonneg = Fraction(0)
        max_signed = Fraction(0)
        primes_wide = tuple(p for p in ps if p > n*n)
        for table in product(range(-1, n+1), repeat=n+1):
            points = {(x, y): 1 for x, y in enumerate(table) if y >= 0}
            if not points:
                continue
            checked += 1
            for p in ps:
                nat, sig, rat, fld, strict = scores(points, p)
                assert strict <= nat <= sig <= rat and sig <= fld
                if p > n:
                    max_nonneg = max(max_nonneg, fld - nat)
                    assert fld - nat <= Fraction(n, n + 1)
                if p in primes_wide:
                    assert fld == rat
                    max_signed = max(max_signed, fld - sig)
                    assert fld - sig <= 1 - Fraction(1, n//2 + 1)
        assert checked == (n + 2)**(n + 1) - 1
        assert max_nonneg == Fraction(n, n + 1)
        assert max_signed == 1 - Fraction(1, n//2 + 1)
        print(f"n={n}: {checked} deterministic restricted tables; "
              f"sharp nonnegative={max_nonneg}, signed={max_signed}")


def weighted():
    ps = (2, 3, 5, 7, 11)
    rows = [(0, 0, 0)] + [v for v in product(range(3), repeat=3) if sum(v) == 2]
    checked = 0
    for table in product(rows, repeat=3):
        points = {(x, y): w for x, row in enumerate(table)
                  for y, w in enumerate(row) if w}
        if not points:
            continue
        checked += 1
        evidence = witness_totals(points, ps)
        lost = 0
        for p in ps:
            nat, sig, rat, fld, strict = scores(points, p)
            d = max(Fraction(0), fld - rat)
            assert evidence[p] >= fld * d*d >= d**3
            lost += fld < rat
        assert lost <= prime_budget(2, ps)
        assert sum(evidence.values()) <= prime_budget(2, ps) + prime_budget(4, ps)
    assert checked == 342
    print("342 randomized restricted tables: exact witness probability, summed budget, and reverse bound PASS")


def sentinels():
    half = {(0, 1): 1, (2, 2): 1}
    assert scores(half, 3) == (Fraction(1, 2), Fraction(1, 2),
                               Fraction(1), Fraction(1), Fraction(1, 2))
    pair_only = {(0, 0): 1, (0, 2): 1}
    assert scores(pair_only, 2)[2:4] == (Fraction(1, 2), Fraction(1))
    assert witness_totals(pair_only, (2,))[2] == Fraction(1, 2)
    assert all(determinants(pts) == 0 for pts in product(pair_only, repeat=3))
    det_only = {(0, 0): 1, (1, 2): 1, (2, 1): 1}
    assert scores(det_only, 3)[2:4] == (Fraction(2, 3), Fraction(1))
    assert witness_totals(det_only, (3,))[3] == Fraction(2, 9)
    assert len({(x % 3, y % 3) for x, y in det_only}) == 3
    negative = {(0, 0): 1, (2, 1): 1}
    assert scores(negative, 2)[2:4] == (Fraction(1), Fraction(1, 2))
    assert scores(negative, 3)[2:4] == (Fraction(1), Fraction(1))
    zero = {(0, 0): 1}
    assert scores(zero, 3)[3:] == (Fraction(1), Fraction(0))
    print("Controls: coefficient obstruction=1/2; pair-only gain=1/2; "
          "determinant-only gain=1/3; reverse loss=1/2; strict-positive gap=1")


if __name__ == "__main__":
    exhaustive()
    weighted()
    sentinels()
