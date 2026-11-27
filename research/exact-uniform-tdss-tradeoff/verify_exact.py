#!/usr/bin/env python3
"""Direct rational formula, posterior flattening, parity, and limit checks."""
from fractions import Fraction as F
from itertools import combinations
from math import comb

HALF = F(1, 2)


def c(n, j):
    return comb(n, j) if 0 <= j <= n else 0


def hyper(n, r, k):
    return [(h, F(c(r, h)*c(n-r, k-h), c(n, k)))
            for h in range(max(0, k+r-n), min(k, r)+1)]


def value(n, k, s, r=None):
    if r is None:
        r = n//2
    if k >= n:
        return F(0)
    return sum(w*abs(s*h/k + (1-s)*(r-h)/(n-k)-HALF)
               for h, w in hyper(n, r, k)) - abs(F(r, n)-HALF)


def zero_threshold(n, k):
    if n % 2 == 0:
        return F(k, n)
    if k <= n//2:
        return F(k+1, n+1)
    return min(F(1), F(k, n-1))


frontier = 0
for n in range(2, 43):
    for k in range(1, n):
        r = n//2
        a = F(k, n)
        z = zero_threshold(n, k)
        hs = hyper(n, r, k)
        assert sum(w for _, w in hs) == 1
        assert sum(h*w for h, w in hs) == F(k*r, n)
        s_grid = sorted({a, (a+z)/2, z, (z+1)/2, F(1)})
        vs = [value(n, k, s) for s in s_grid]
        assert vs == sorted(vs)
        for s, v in zip(s_grid, vs):
            assert (v == 0) == (s <= z)
            assert v >= 0
            frontier += 1

rec = 0
for n in range(2, 65):
    row = [value(n, k, F(1)) for k in range(1, n+1)]
    assert row[0] == F(n//2, n)
    assert row[-1] == 0
    for j in range(1, n):
        correction = F(0)
        if j % 2:
            h = (j+1)//2
            m = n//2
            correction = F(c(m, h)*c(n-m, h), c(n, j+1)*2*j)
        assert row[j-1]-row[j] == correction
        rec += 1

for n, expected in [(1, [F(0)]), (4, [HALF, F(1, 6), F(1, 6), F(0)]),
                    (5, [F(2, 5), F(1, 10), F(1, 10), F(0), F(0)])]:
    assert [value(n, k, F(1)) for k in range(1, n+1)] == expected

binchecks = limitchecks = 0
for k in range(1, 65):
    r = k//2
    b = F(c(2*r, r), 2*4**r)
    pvalues = []
    for j in range(13):
        p = F(j, 24)
        expectation = sum(c(k, h)*p**h*(1-p)**(k-h)*abs(F(h, k)-HALF)
                          for h in range(k+1)) - (HALF-p)
        pvalues.append(expectation)
        binchecks += 1
    assert pvalues == sorted(pvalues) and pvalues[-1] == b
    for n in [2*(k+1), 4*k*k, 32*k*k]:
        v = value(n, k, F(1))
        # Bounded test function gives at most (1/2)*collision TV error.
        assert 0 <= b-v <= F(k*(k-1), 4*n)
        limitchecks += 1


def compositions(n, delim):
    for cuts in combinations(range(delim+n-1), n-1):
        bounds = (-1, *cuts, delim+n-1)
        yield tuple(b-a-1 for a, b in zip(bounds, bounds[1:]))


flatten = comparisons = 0
for n in range(2, 7):
    for raw in compositions(n, 6):
        q = tuple(F(x, 6) for x in sorted(raw, reverse=True))
        r = n//2
        f = sum(abs(sum(q[i] for i in subset)-HALF)
                for subset in combinations(range(n), r))/c(n, r)
        for k in range(1, n):
            s = sum(q[:k])
            assert f-abs(F(r, n)-HALF) >= value(n, k, s)
            flatten += 1
    for k in range(1, n):
        for s in [F(k, n), (F(k, n)+1)/2, F(1)]:
            g = [value(n, k, s, r) for r in range(n+1)]
            assert g == g[::-1] and g[:n//2+1] == sorted(g[:n//2+1])
            comparisons += len(g)

assert value(3, 2, F(1)) == 0
p = F(1, 3)
iid = sum(c(2, h)*p**h*(1-p)**(2-h)*abs(F(h, 2)-HALF)
          for h in range(3)) - abs(p-HALF)
assert iid == F(1, 9) > value(3, 2, F(1))
print(f"exact PASS: {frontier} frontier points, {rec} deletion pairs, "
      f"{binchecks} binomial points, {limitchecks} limit bounds")
print(f"exact PASS: {flatten} posterior flattenings, {comparisons} size comparisons")
