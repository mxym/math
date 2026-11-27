#!/usr/bin/env python3
"""Replay only synthetic probability identities and Gaussian grid quadrature."""
from fractions import Fraction as F
from itertools import product
from math import ceil, erf, exp, lcm, log, pi, sqrt

exact_checks = 0
numerical_checks = 0


def exact(c):
    assert c
    global exact_checks
    exact_checks += 1


def numerical(c):
    assert c
    global numerical_checks
    numerical_checks += 1


def exact_caps(rows, removal):
    # Finite joint pmf with equal-sized output alphabet in each column.
    # Compare descending slopes against exhaustive integral cap budgets.
    n = len(rows[0])
    total = sum(map(sum, rows))
    factor = lcm(*range(1, n + 1))
    den = total * factor
    target = (total - removal) * factor
    p = tuple(tuple(a * factor for a in row) for row in rows)
    segments = []
    for row in p:
        levels = sorted(set((*row, 0)))
        for left, right in zip(levels, levels[1:]):
            segments.append((sum(a > left for a in row), right - left))
    remaining = target
    cap = 0
    for slope, length in sorted(segments, reverse=True):
        gain = min(slope * length, remaining)
        cap += F(gain, slope)
        remaining -= gain
        if not remaining:
            break
    exact(remaining == 0 and cap.denominator == 1)
    cap = max(int(cap), den // n)
    brute = None
    for caps in product(range(den + 1), repeat=len(p)):
        s = sum(caps)
        if s < den // n or brute is not None and s >= brute:
            continue
        if sum(sum(min(a, c) for a in row) for row, c in zip(p, caps)) >= target:
            brute = s
    exact(brute == cap)
    return cap


for p in [
    ((3, 0, 2), (0, 3, 1)),
    ((0, 1, 2), (3, 1, 0)),
    ((4, 0), (1, 5)),
    ((1, 1, 1), (5, 0, 0)),
    ((5, 3, 2), (3, 3, 3)),
    ((1, 0), (0, 2), (1, 2)),
    ((0, 0), (0, 4), (2, 1)),
]:
    last = None
    for e in range(sum(map(sum, p)) + 1):
        cap = exact_caps(p, e)
        exact(last is None or cap <= last)
        last = cap


# Exact completion-square differences: L=Z^2, M=Z, T=(1/2,1/3).
# Posterior support translations are cosets of 2Z x 3Z (index 6).
T = [F(1, 2), F(1, 3)]
Ainv = [[3, 1], [1, 2]]
Binv = F(5, 7)
m = [F(1, 7), F(-1, 5)]
dot = lambda u, v: sum(a * b for a, b in zip(u, v))
quad = lambda D, x: dot(x, [dot(row, x) for row in D])
prec = [[Ainv[i][j] + Binv * T[i] * T[j] for j in range(2)] for i in range(2)]
det = prec[0][0] * prec[1][1] - prec[0][1] * prec[1][0]
for v in product(range(-12, 13), repeat=2):
    exact((dot(T, v).denominator == 1) == (v[0] % 2 == v[1] % 3 == 0))
for y in [F(-3, 7), F(1, 6), F(2, 3), F(3, 2)]:
    force = [dot(row, m) + Binv * y * T[i] for i, row in enumerate(Ainv)]
    center = [
        (prec[1][1] * force[0] - prec[0][1] * force[1]) / det,
        (prec[0][0] * force[1] - prec[1][0] * force[0]) / det,
    ]
    rem = []
    for x in product(range(-6, 7), repeat=2):
        xx = [F(i) - j for i, j in zip(x, m)]
        zz = [F(i) - j for i, j in zip(x, center)]
        rem.append(quad(Ainv, xx) + Binv * (y - dot(T, x)) ** 2 - quad(prec, zz))
    exact(len(set(rem)) == 1)


def profile(r, a):
    if a == 0:
        return 1.
    if a == 1:
        return 0.
    t = -log(a)
    if r == 1:
        return erf(sqrt(t)) - 2 * a * sqrt(t / pi)
    if r == 2:
        return 1 - a - a * t
    assert r == 3
    return erf(sqrt(t)) - 2 * a * sqrt(t / pi) - 4 * a * t ** 1.5 / (3 * sqrt(pi))


def quadrature(r, step, shift, shear):
    # Orthogonal grid, optionally sheared on x by + shear*y.
    # determinant is step^r; half the sum of basis lengths bounds the radius.
    radius = step * (r - 1 + sqrt(1 + shear * shear)) / 2
    N = ceil(10 / step)
    vals = []
    for idx in product(range(-N, N + 1), repeat=r):
        z = [step * (i + s) for i, s in zip(idx, shift)]
        if r >= 2:
            z[0] += shear * z[1]
        vals.append(exp(-pi * dot(z, z)))
    beta = step ** r
    norm = beta * sum(vals)
    numerical(abs(norm - 1) < 2e-7)
    worst = 0.
    for a in [0., .001, .02, .165, .4, .777, .91, 1.]:
        f = profile(r, a)
        raw = beta * sum(max(x - a, 0) for x in vals)
        conditional = beta * sum(max(x / norm - a, 0) for x in vals)
        err = max(abs(raw - f), abs(conditional - f)) / radius**2
        worst = max(worst, err)
        numerical(err < 3.)  # empirical check, not the analytic universal bound
    return worst


worst = max(
    quadrature(r, step, tuple(0.191 * (j+1) if shift else 0. for j in range(r)), shear)
    for r, step, shear in [
        (1, .2, 0.), (1, .089, 0.), (1, .036, 0.),
        (2, .24, 0.), (2, .12, .6), (2, .075, -.43),
        (3, .4, 0.), (3, .32, .4),
    ]
    for shift in [0, 1]
)
print(f'PASS: {exact_checks} exact rational checks, {numerical_checks} numerical profile checks')
print(f'Largest sampled clipped quadrature error divided by h^2 upper bound: {worst:.6f}')
