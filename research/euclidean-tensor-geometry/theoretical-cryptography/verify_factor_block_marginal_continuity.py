#!/usr/bin/env python3
"""Exact rational checks for prescribed block-marginal continuity."""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from random import Random

checks = 0
noncommuting = 0


def ok(value):
    global checks
    checks += 1
    if not value:
        raise AssertionError("exact check failed")


def eq(x, y):
    global checks
    checks += 1
    if x != y:
        raise AssertionError((x, y))


@lru_cache(None)
def pf(n):
    """Prime exponent vector of a positive integer."""
    out = {}
    j = 2
    while j * j <= n:
        while n % j == 0:
            n //= j
            out[j] = out.get(j, 0) + 1
        j += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def log_form(terms):
    """Canonical expression sum_p coefficient[p] log(p), exactly."""
    out = defaultdict(F)
    for coef, x in terms:
        if not coef:
            continue
        x = F(x)
        for p, a in pf(x.numerator).items():
            out[p] += coef * a
        for p, a in pf(x.denominator).items():
            out[p] -= coef * a
    return {p: a for p, a in out.items() if a}


def eterms(weights, factor=1):
    return [(-factor * z, z) for z in weights if z]


def water(p, K, delta):
    grid = [F(0)] + sorted(set(x / k for x, k in zip(p, K)))
    for lo, hi in zip(grid, grid[1:]):
        active = [i for i in range(len(p)) if p[i] / K[i] > lo]
        n = sum(K[i] for i in active)
        if n <= 1:
            continue
        inactive = sum(x for i, x in enumerate(p) if i not in active)
        c = (delta - inactive) / (n - 1)
        if lo <= c <= hi:
            mu = [min(x, k * c) for x, k in zip(p, K)]
            return c, mu, (1 - delta) / c
    raise AssertionError("no water level")


def quantum_pair(p, ds, delta):
    K = [d * d for d in ds]
    expanded = [x / k for x, k in zip(p, K) for _ in range(k)]
    sat = 1 - max(expanded)
    m = len(p)
    sigma = {(j, j, 0): p[j] for j in range(m)}
    if not delta or not sat:
        return
    if delta >= sat:
        j = max(range(m), key=lambda i: p[i] / K[i])
        rho = {(i, j, h): p[i] / (ds[i] * ds[j])
               for i in range(m) for h in range(ds[i] * ds[j])}
        b_rho = [F(1, ds[j])] * ds[j]
        curve = eterms(expanded)
        distance = sat
    else:
        c, mu, L = water(p, K, delta)
        ell = 1 - delta - c
        t = [(x - y) / ell for x, y in zip(p, mu)]
        eq(sum(mu) - c, delta)
        eq(sum(t), 1)
        ok(min(t) >= 0 and L > 1)
        rho = {}
        for j in range(m):
            if not t[j]:
                continue
            rho.update({(j, j, h): t[j] * (1 - delta if h == 0 else c)
                        for h in range(K[j])})
            for i in range(m):
                if i != j:
                    rho.update({(i, j, h): t[j] * mu[i] / (ds[i] * ds[j])
                                for h in range(ds[i] * ds[j])})
        b_rho = [t[j] / ds[j] for j in range(m) for _ in range(ds[j])]
        w = [c0 / k for c0, k in zip(mu, K) for _ in range(k)]
        w[w.index(c)] = 1 - delta
        eq(sum(w), 1)
        curve = eterms(w)
        dual = [(-x, y / k) for x, y, k in zip(p, mu, K)]
        dual.append((-(1 - delta), L))
        eq(log_form(curve), log_form(dual))
        distance = delta
    eq(sum(rho.values()), 1)
    eq(sum(b_rho), 1)
    for i in range(m):
        eq(sum(x for (u, _, _), x in rho.items() if u == i), p[i])
    for j in range(m):
        col = sum(x for (_, v, _), x in rho.items() if v == j)
        eq(col, sum(b_rho[sum(ds[:j]):sum(ds[:j+1])])
            if delta < sat else (1 if rho.get((0, j, 0), 0) else 0))
    metric = sum(abs(rho.get(z, 0) - sigma.get(z, 0))
                 for z in (rho.keys() | sigma.keys())) / 2
    eq(metric, distance)
    b_sigma = [p[j] / ds[j] for j in range(m) for _ in range(ds[j])]
    gap = (eterms(rho.values()) + eterms(b_rho, -1)
           + eterms(sigma.values(), -1) + eterms(b_sigma))
    eq(log_form(gap), log_form(curve))


def psd(a):
    """Exact PSD test for a symmetric rational matrix, by Schur complements."""
    if any(a[i][i] < 0 for i in range(len(a))):
        return False
    if not a:
        return True
    k = next((i for i in range(len(a)) if a[i][i] > 0), None)
    if k is None:
        return not any(x for row in a for x in row)
    ix = [j for j in range(len(a)) if j != k]
    return psd([[a[i][j]-a[i][k]*a[k][j]/a[k][k] for j in ix] for i in ix])


def sc(x, a):
    return [[x * y for y in row] for row in a]


def add(a, b):
    return [[x+y for x, y in zip(u, v)] for u, v in zip(a, b)]


def sub(a, b):
    return add(a, sc(-1, b))


def partial(a, d, b):
    return [[sum(a[k*b+i][k*b+j] for k in range(d)) for j in range(b)]
            for i in range(b)]


def pi_tensor(a, d, b):
    return [[a[i % b][j % b] / d if i//b == j//b else F(0)
             for j in range(d*b)] for i in range(d*b)]


def compare_operators(rng, ds, b, p, q):
    global noncommuting
    K = [d * min(d, b) for d in ds]
    sat = 1-max(x / k for x, k in zip(p, K))
    if not sat:
        return
    delta = sat * F(3, 7)
    c, mu, L = water(p, K, delta)
    sig = []
    for d, weight in zip(ds, q):
        n = d*b
        G = [[rng.randrange(-4, 5) for _ in range(3)] for _ in range(n)]
        # Include a nonzero diagonal without making the matrix commute
        # with the later reference.
        A = [[sum(x*y for x, y in zip(G[i], G[j])) + int(i == j)
              for j in range(n)] for i in range(n)]
        sig.append(sc(weight / sum(A[i][i] for i in range(n)), A))
    B = [[F(0) for _ in range(b)] for _ in range(b)]
    for d, A in zip(ds, sig):
        B = add(B, partial(A, d, b))
    tauB = [[F(0) for _ in range(b)] for _ in range(b)]
    for d, k, mu_i, sig_i in zip(ds, K, mu, sig):
        W = sc(mu_i, pi_tensor(B, d, b))
        n = d*b
        if any(sum(W[i][j]*sig_i[j][h] - sig_i[i][j]*W[j][h] for j in range(n))
               for i in range(n) for h in range(n)):
            noncommuting += 1
        tau = add(W, sc((L - 1) * mu_i / k, sig_i))
        ok(psd(sub(tau, W)))
        ok(psd(sub(sc(L, W), tau)))
        ok(psd(sub(tau, sc(L * mu_i / k, sig_i))))
        tauB = add(tauB, partial(tau, d, b))
    ok(psd(sub(B, tauB)))
    rs = [min(d, b) for d in ds]
    direct = ([(-x, y / k) for x, y, k in zip(q, mu, K)]
              + [(-(x-z), y / d) for x, z, y, d in zip(p, q, mu, ds)])
    target = ([(-x, y / k) for x, y, k in zip(p, mu, K)]
              + [(z-x, r) for x, z, r in zip(p, q, rs)])
    eq(log_form(direct), log_form(target))


def probabilities(weights):
    return [F(x, sum(weights)) for x in weights]


def main():
    rng = Random(20261127)
    fixtures = [([1, 1], [1, 3]), ([2], [1]), ([1, 3], [2, 5]),
                ([1, 2, 4], [7, 4, 3]), ([2, 3, 1], [3, 3, 3]),
                ([1, 1, 1, 1], [1, 2, 5, 10])]
    for _ in range(90):
        m = rng.randrange(1, 5)
        fixtures.append(([rng.randrange(1, 5) for _ in range(m)],
                         [rng.randrange(1, 17) for _ in range(m)]))
    actual = 0
    for ds, w in fixtures:
        p = probabilities(w)
        K = [d*d for d in ds]
        sat = 1-max(x / k for x, k in zip(p, K))
        markers = {F(0), sat, F(1), sat/7, sat/3, sat/2, sat*F(5, 6)}
        for x, k in zip(p, K):
            c = x / k
            q = sum(min(y, h*c) for y, h in zip(p, K))-c
            if 0 <= q <= sat:
                markers.add(q)
        for delta in sorted(markers):
            quantum_pair(p, ds, delta)
            actual += 1
    for _ in range(70):
        m, b = rng.randrange(1, 5), rng.randrange(1, 5)
        ds = [rng.randrange(1, 4) for _ in range(m)]
        p = probabilities([rng.randrange(1, 13) for _ in range(m)])
        q = probabilities([rng.randrange(1, 13) for _ in range(m)])
        compare_operators(rng, ds, b, p, q)
    ok(noncommuting > 0)
    print(f"Block-marginal continuity checks passed: {checks}; "
          f"{actual} sharpness budgets and 70 rational anchor fixtures "
          f"({noncommuting} noncommuting blocks).")


if __name__ == "__main__":
    main()
