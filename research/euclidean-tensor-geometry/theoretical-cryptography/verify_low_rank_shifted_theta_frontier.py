#!/usr/bin/env python3
"""Finite audits of rounding and constants for a standalone positive theta sum."""
from collections import defaultdict
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from itertools import product
from math import prod
from random import Random


def dec(x):
    x = F(x)
    return D(x.numerator) / D(x.denominator)


def quadratic(c, z):
    return sum(x * c[i][j] * z[j]
               for i, x in enumerate(z) for j in range(len(z)))


def adder(i, j):
    return tuple(a + b for a, b in zip(i, j))


def boxes():
    rng = Random(1516)
    rows = cases = collisions = 0
    for case in range(44):
        n, r = 2 + case % 3, 1 + case % 2
        C = tuple(tuple(F(i == j) * (-1 if (case + i) % 2 else 1)
                        if i == j else F(case % 3 - 1, 3)
                        for j in range(r)) for i in range(r))
        U = tuple(tuple(F(rng.randrange(-4, 5), 6) for _ in range(r))
                  for _ in range(n))
        beta = tuple(F(3) + F(rng.randrange(4), 3) for _ in range(n))
        theta = tuple(F(rng.randrange(9), 9) for _ in range(n))
        # Finite test boxes may be smaller than the proof's certified tail radius.
        R, B, eps = 2, 4, F(1, 2)
        cap = eps / (32 * r * r * B * n * n * (B * R + 1))
        delta = F(1)
        while delta > cap:
            delta /= 2
        basis = []
        for v, t in zip(U, theta):
            basis.append(tuple((x - t, tuple(int(a * (x - t) // delta)
                                             for a in v))
                               for x in range(-R, R + 2)
                               if abs(x - t) <= R))
        with localcontext() as ctx:
            ctx.prec = 45
            direct = D(0)
            bins_direct = defaultdict(D)
            for choice in product(*basis):
                ys, inds = zip(*choice)
                z = tuple(sum(U[i][j] * ys[i] for i in range(n))
                          for j in range(r))
                key = tuple(sum(ind[j] for ind in inds) for j in range(r))
                new = tuple(delta * k for k in key)
                loss = abs(quadratic(C, z) - quadratic(C, new))
                assert loss <= r * r * B * n * n * (2 * B * R * delta + delta ** 2)
                assert loss < eps / 16
                unary = sum(b * y * y for b, y in zip(beta, ys))
                direct += dec(-unary - quadratic(C, z)).exp()
                bins_direct[key] += dec(-unary).exp()
                rows += 1
            bins = {(0,) * r: D(1)}
            for beta_i, support in zip(beta, basis):
                nxt = defaultdict(D)
                for k, mass in bins.items():
                    for y, key in support:
                        nxt[adder(k, key)] += mass * dec(-beta_i * y * y).exp()
                bins = nxt
            assert bins.keys() == bins_direct.keys()
            assert all(abs(bins[k] / v - 1) < D("1e-40")
                       for k, v in bins_direct.items())
            value = sum(v * dec(-quadratic(C, tuple(delta * x for x in k))).exp()
                        for k, v in bins.items())
            assert abs((value / direct).ln()) < dec(eps) / 16
            collisions += prod(map(len, basis)) - len(bins)
            cases += 1
    return cases, rows, collisions


def coeffs(weights, ell, base):
    m, J = len(weights), len(weights) * (ell - 1)
    co = [[0] * ell for i in weights]
    for i, w in enumerate(weights):
        co[i][0] = w * base ** J
        for k in range(1, ell):
            pw = base ** (i * (ell - 1) + k - 1)
            co[i][k] = pw
            co[i][0] -= pw
    return tuple(v for row in co for v in row)


def radix():
    # Test equality detection and bit slices, not a generic partition solver.
    rng = Random(5419)
    rows = flat = 0
    for m, ell in ((1, 2), (2, 2), (2, 3), (3, 2)):
        radius = 3
        base = 8 * radius
        for _ in range(7):
            w = tuple(rng.randrange(1, 6) for i in range(m))
            co = coeffs(w, ell, base)
            J = m * (ell - 1)
            expected = 0
            observed = 0
            for x in product(range(1 - radius, radius + 1), repeat=m * ell):
                score = sum(a * (2 * v - 1) for a, v in zip(co, x))
                et = 2 * sum(base ** (i * (ell - 1) + k - 1)
                             * (x[i * ell + k] - x[i * ell])
                             for i in range(m) for k in range(1, ell))
                et += base ** J * sum(w[i] * (2 * x[i * ell] - 1)
                                      for i in range(m))
                assert score == et
                repeated = all(x[i * ell + k] == x[i * ell]
                               for i in range(m) for k in range(1, ell))
                assert (score == 0) == (repeated and
                    sum(w[i] * (2 * x[i * ell] - 1) for i in range(m)) == 0)
                rows += 1
            for bits in product((0, 1), repeat=m):
                s = sum(a * (2 * bits[i // ell] - 1)
                        for i, a in enumerate(co))
                expected += not sum(a * (2 * b - 1) for a, b in zip(w, bits))
                observed += s == 0
                flat += 1
            assert expected == observed
    return rows, flat


def tails():
    checks = 0
    # Rational inequalities imply all three margins by log(5)<2, log(2)<1.
    for m in range(1, 801):
        ell = 16 * (m + 1)
        n = m * ell
        R = n + 1
        # Each normalized contribution is bounded above by exp(-5) < 1/32.
        assert 2 * n + F(n, 4) - F(R * R, 2) < -5
        assert 2 * n + F(n, 4) - n ** 2 < -5
        # 2^m 4m <= exp(m+2+m), with log(m)<=m.
        assert m + 2 + m - 2 * ell < -5
        assert 1 + m - 2 * ell < 0  # 2m exp(-2 ell)<1
        checks += 4
    return checks



def rank(mat):
    a = [list(map(F, row)) for row in mat]
    i = 0
    for j in range(len(a[0])):
        pivot = next((k for k in range(i, len(a)) if a[k][j]), None)
        if pivot is None:
            continue
        a[i], a[pivot] = a[pivot], a[i]
        t = a[i][j]
        for k in range(i + 1, len(a)):
            if a[k][j]:
                z = a[k][j] / t
                a[k] = [v - z * w for v, w in zip(a[k], a[i])]
        i += 1
    return i


def dyadic():
    rng = Random(391)
    count = 0
    for n in (2, 4, 8, 16):
        for i in range(48):
            c = [rng.randrange(-2, 3) for _ in range(n)]
            if not any(c[1:]):
                c[-1] = 1
            # Multiplication by a nonconstant polynomial mod X^n+1.
            q = [[(1 if k >= j else -1) * c[(k-j) % n]
                  for j in range(n)] for k in range(n)]
            d = [rng.randrange(2 + i % n) for j in range(n)]
            s = rank([[q[x][y] - (d[x] if x == y else 0)
                       for y in range(n)] for x in range(n)])
            ms = [d.count(a) for a in set(d)]
            assert max(ms) <= s
            counts = [sum(d[x] != d[(x + j) % n] for x in range(n))
                      for j in range(n)]
            assert sum(counts) == n * n - sum(k * k for k in ms)
            assert max(counts) <= 2 * s and 3 * s >= n
            count += 1
    return count


if __name__ == "__main__":
    A, B, C = boxes()
    P, Q = radix()
    T, J = tails(), dyadic()
    assert C > 0
    print("PASS: boxes/rational mesh rows/bin collisions/radix rows/flat rows/tails/dyadic")
    print(A, B, C, P, Q, T, J)
