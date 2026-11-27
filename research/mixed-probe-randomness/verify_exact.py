#!/usr/bin/env python3
"""Exact checks of scalar factors, positivity, and rational witness data."""
from fractions import Fraction as Q
from itertools import product

I = ((Q(1), Q(0)), (Q(0), Q(1)))
X = ((Q(0), Q(1)), (Q(1), Q(0)))
Z = ((Q(1), Q(0)), (Q(0), Q(-1)))

def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))

def ma(a, b, x=1, y=1):
    return tuple(tuple(x * a[i][j] + y * b[i][j] for j in range(2))
                 for i in range(2))

def tr(a):
    return a[0][0] + a[1][1]

def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]

def psd(a):
    return a[0][1] == a[1][0] and min(a[0][0], a[1][1], det(a)) >= 0

rs = [Q(0), Q(1, 5), Q(3, 5), Q(15, 17), Q(1)]
slopes = [Q(-1), Q(-3, 7), Q(0), Q(1, 3), Q(1, 2), Q(1)]
zs = [Q(-1), Q(-1, 4), Q(0), Q(2, 3), Q(1)]
count = 0
x_plus, x_minus = ma(I, X, Q(1, 2), Q(1, 2)), ma(I, X, Q(1, 2), -Q(1, 2))
for r, a, zfrac in product(rs, slopes, zs):
    # Rational parametrization of the full signed transverse segment.
    t, s = 2*a/(1+a*a), (1-a*a)/(1+a*a)
    z = s*zfrac
    w = (1+zfrac)/2
    rho = ma(I, Z, Q(1, 2), r/2)
    j1, j2 = ma(X, Z, t, s), ma(X, Z, t, -s)
    ave = ma(j1, j2, w, 1-w)
    m = ma(I, ave, Q(1, 2), Q(1, 2))
    assert psd(rho) and psd(m) and psd(ma(I, m, 1, -1)) and 0 <= w <= 1
    assert tr(mm(x_plus, m)) - tr(mm(x_minus, m)) == t
    assert tr(mm(x_plus, m)) + tr(mm(x_minus, m)) == 1
    assert tr(mm(rho, m)) == (1 + r*z) / 2
    comm = ma(mm(rho, m), mm(m, rho), 1, -1)
    # For this real 2x2 skew matrix, ||[rho,M]||_1^2=4 det([rho,M]).
    assert 4 * det(comm) == (r*t)**2
    for j in (j1, j2):
        assert mm(j, j) == I
        # sqrt(rho) J sqrt(rho) has the same trace and determinant as rho J;
        # this avoids irrational square roots in the exact checker.
        tmat = mm(rho, j)
        assert det(tmat) <= 0
        assert tr(tmat)**2 - 4*det(tmat) == 1 - (r*t)**2
        delta = ma(rho, mm(mm(j, rho), j), 1, -1)
        assert tr(delta) == 0 and -det(delta) == (r*t)**2
    count += 1
print(f"exact rational qubit data, PSD, commutator, and Helstrom squares: {count} PASS")

cdf_count = 0
vals = [Q(0), Q(1, 7), Q(3, 5), Q(1)]
for effects in product(vals, repeat=4):
    edges = sorted(set((Q(0), Q(1), *effects)))
    intervals = [(y-x, (x+y)/2) for x,y in zip(edges, edges[1:])]
    assert len(intervals) <= len(effects)+1
    assert sum(w for w,_ in intervals) == 1
    for m in effects:
        assert sum(w for w,u in intervals if u <= m) == m
    cdf_count += 1
print(f"finite commuting threshold decompositions: {cdf_count} PASS")

r, t = Q(3, 5), Q(4, 5)
rad = 1-(r*t)**2
assert rad == Q(481, 625) < Q(22, 25)**2
assert rad > 1-(2*r*t)**2  # factor-of-two negative control
assert (1-(0*t)**2) == (1-(r*0)**2) == 1
assert 1-Q(1)**2 == 0
print("mixed positive example, vanishing contrasts, and factor-of-two negative control: PASS")
