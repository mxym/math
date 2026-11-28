#!/usr/bin/env python3
"""Finite coefficient identity checks plus separate small Gaussian sanity tests."""

from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial
from random import Random

import mpmath as mp

R = Random(650883)
mp.mp.dps = 65


def caps_parts(total, k):
    if k == 0:
        if total == 0:
            yield ()
        return
    for b in range(total+1):
        for rest in caps_parts(total-b, k-1):
            yield (b,)+rest


def log_series(b):
    L = len(b)-1
    assert b[0] == 1
    if not any(b[1:]):
        return [0]*(L+1)
    a = [0]*(L+1)
    if L:
        a[1] = b[1]
    for j in range(2, L+1):
        a[j] = b[j]-sum(k*a[k]*b[j-k] for k in range(1, j))/j
    return a


def e_coeff(E, couplings, mom, L):
    out = [1]
    for k in range(1, L+1):
        val = 0
        for powers in caps_parts(k, len(E)):
            deg = [0]*len(mom)
            w = 1
            for (i, j), m in zip(E, powers):
                deg[i] += m
                deg[j] += m
                w *= (-couplings[i, j])**m/factorial(m)
            for i, d in enumerate(deg):
                w *= mom[i][d]
            val += w
        out.append(val)
    return out


def direct_coeff(E, couplings, src, L):
    if not E:
        return [1]+[0]*L
    zero = (src[0][0][0]*0)
    out = [zero]*(L+1)
    for values in product(*src):
        x, w = zip(*values)
        v = 1
        for u in w:
            v *= u
        t = -sum(couplings[i, j]*x[i]*x[j] for i, j in E)
        val = v
        for k in range(L+1):
            out[k] += val
            val *= t/(k+1)
    return out


def connected(E):
    if not E:
        return False
    V = set(E[0])
    for _ in E:
        for e in E:
            if V.intersection(e):
                V.update(e)
    return all(set(e) <= V for e in E)


poly_ensembles = coef_cases = pieces = cancel_cases = 0
for n in range(2, 6):
    for trial in range(18):
        edges = tuple(e for e in combinations(range(n), 2) if R.random() < 0.55)
        JC = {e: Q(R.randrange(-5, 6), R.randrange(17, 36)) for e in edges}
        src = []
        L = 5
        for i in range(n):
            theta = Q(R.randrange(-2, 3), 4)
            counts = [R.randrange(1, 9) for _ in range(3)]
            src.append(tuple((h-theta, Q(counts[h+1], sum(counts)))
                             for h in (-1, 0, 1)))
        mom = [[sum(w*x**k for x, w in site) for k in range(L+1)] for site in src]
        expected = log_series(direct_coeff(edges, JC, src, L))
        assert log_series(e_coeff(edges, JC, mom, L)) == expected
        local = {}
        for k in range(min(L, len(edges))+1):
            for T in combinations(edges, k):
                local[T] = log_series(e_coeff(T, JC, mom, L))
                pieces += 1
        got = [0]*(L+1)
        for S, v in local.items():
            if not S:
                continue
            z = [0]*(L+1)
            for t in range(len(S)+1):
                for T in combinations(S, t):
                    for j, u in enumerate(local[T]):
                        z[j] += (-1)**(len(S)-t)*u
            assert all(x == 0 for x in z[:len(S)])
            if connected(S):
                got = [a+b for a, b in zip(got, z)]
            else:
                assert not any(z)
                cancel_cases += 1
        assert expected == got
        poly_ensembles += 1
        coef_cases += L+1


def plain(A, beta, theta, J, z, L=8, residues=None):
    out = mp.mpc(0)
    for x in product(range(-L, L+1), repeat=len(beta)):
        if residues and any(x[i] % q != v for i, q, v in residues):
            continue
        u = [v-th for v, th in zip(x, theta)]
        base = sum(b*w*w for b, w in zip(beta, u))
        shift = sum(J[e]*u[e[0]]*u[e[1]] for e in A)
        out += mp.exp(-base-z*shift)
    return out


beta = [mp.mpf(1), mp.mpf(4)/3, mp.mpf(5)/4]
theta = [mp.mpf(1)/3, -mp.mpf(1)/5, mp.mpf(1)/4]
A = tuple(combinations(range(3), 2))
J = {e: mp.mpf(s)*mp.mpf("0.000002") for s, e in zip((1, -1, 1), A)}
src = []
for b, h in zip(beta, theta):
    w = [mp.exp(-b*(i-h)**2) for i in range(-8, 9)]
    src.append(tuple((i-h, u/sum(w)) for i, u in zip(range(-8, 9), w)))
site = plain((), beta, theta, J, 0)
part = plain(A, beta, theta, J, 1)/site
assert abs(part.imag) == 0
mom = [[sum(w*x**k for x, w in v) for k in range(8)] for v in src]
m_log = log_series(e_coeff(A, J, mom, 7))
assert abs(mp.log(part.real)-sum(m_log)) < mp.mpf("1e-35")
zetas = (2j, -2, 2, mp.mpc(1, 1))
for z in zetas:
    rat = plain(A, beta, theta, J, z)/plain(((1, 2),), beta, theta, J, z)
    assert abs(rat-1) < mp.mpf("0.001")

# Exact algebraic substitution of a residue cylinder, done on the same
# finite box here (the paper's proof reindexes the whole infinite sum).
old = plain(A, beta, theta, J, 1, residues=((0, 3, 2),))
q, a = 3, 2
new = mp.mpf(0)
for ys in product(range(-8, 9), repeat=3):
    if not -8 <= q*ys[0]+a <= 8:
        continue
    u = (ys[0]-(theta[0]-a)/q, ys[1]-theta[1], ys[2]-theta[2])
    b = (q*q*beta[0], beta[1], beta[2])
    j = {e: J[e]*(q if 0 in e else 1) for e in A}
    new += mp.exp(-sum(bi*ui**2 for bi, ui in zip(b, u))
                  -sum(j[e]*u[e[0]]*u[e[1]] for e in A))
assert abs(old.real-new) < mp.mpf("1e-62")

print("PASS: exact graph ensembles/coefs/subsets/cancellations, Gaussian comparisons")
print(poly_ensembles, coef_cases, pieces, cancel_cases, len(zetas)+2)
