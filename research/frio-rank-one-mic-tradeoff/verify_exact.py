#!/usr/bin/env python3
"""Exact rational checks, with Gaussian-rational entries for complex effects."""
from fractions import Fraction as F
from itertools import product

ZERO = (F(0), F(0))
PHASE = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def scale(z, a):
    return z[0]*a, z[1]*a


def mul(z, w):
    return z[0]*w[0] - z[1]*w[1], z[0]*w[1] + z[1]*w[0]


def conj(z):
    return z[0], -z[1]


def add(z, w):
    return z[0]+w[0], z[1]+w[1]


def csum(values):
    u = ZERO
    for x in values:
        u = add(u, x)
    return u


def dot(v, w):
    return csum(mul(conj(a), b) for a, b in zip(v, w))


def effect(v, weight):
    return [[scale(mul(a, conj(b)), weight) for b in v] for a in v]


def fourier_frame(d, repeat=False, imbalanced=False):
    for i in range(4):
        v = [PHASE[i*j % 4] for j in range(d)]
        if repeat:
            parts = [F(1, 8), F(1, 8)] if not imbalanced else [F(1, 12), F(1, 6)]
        else:
            parts = [F(1, 4)]
        for a in parts:
            yield v, a


def rational_det(rows):
    h = [[F(z) for z in row] for row in rows]
    out = F(1)
    for j in range(len(h)):
        pivot = next((i for i in range(j, len(h)) if h[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            h[j], h[pivot] = h[pivot], h[j]
            out = -out
        out *= h[j][j]
        for i in range(j+1, len(h)):
            c = h[i][j] / h[j][j]
            h[i] = [x-c*y for x, y in zip(h[i], h[j])]
    return out


def check():
    cases = passed_balanced = passed_strict = support_cases = 0
    specs = [
        [F(1)], [F(1), F(0)], [F(4, 5), F(3, 5)],
        [F(4, 5), F(3, 5), F(0)],
        [F(2, 7), F(3, 7), F(6, 7)],
        [F(2, 7), F(3, 7), F(6, 7), F(0)],
        [F(1, 3), F(2, 3), F(2, 3), F(0)],
        [F(1, 2)]*4,
    ]
    for spec in specs:
        d = len(spec)
        r = sum(x > 0 for x in spec)
        assert sum(x*x for x in spec) == 1 and all(x > 0 for x in spec[:r])
        us = set(spec + [max(spec)*F(t, 30) for t in range(31)])
        for repeat, unequal in [(False, False), (True, False), (True, True)]:
            frame = list(fourier_frame(d, repeat, unequal))
            m = [effect(v, w) for v, w in frame]
            n = len(m)
            assert n in (4, 8) and n >= d
            for j, k in product(range(d), repeat=2):
                assert csum(x[j][k] for x in m) == (F(j == k), F(0))
            for u in sorted(us):
                h = [min(x, u) for x in spec]
                s = sum(y*y for y in h)
                base = sum(h)**2/n
                assert 0 <= s <= 1 and s/n <= base <= r*s/n
                if u == max(spec):
                    assert s == 1
                    assert h == spec
                if u <= min(spec[:r]):
                    assert base == r*s/n
                if s == 0:
                    assert base == 0
                    continue
                if r < d:
                    support_cases += 1
                    assert all(y == 0 for y in h[r:])
                alpha = sum(h)/n
                mu = alpha/u
                fs = [h[j]/spec[j] for j in range(r)]
                diag_d = [alpha*spec[j]**2/h[j] for j in range(r)]
                diag_y = [diag_d[j]-mu*spec[j]**2 for j in range(r)]
                assert all(0 <= x <= 1 for x in fs)
                assert all(y >= 0 and y*(1-f**2) == 0 for y, f in zip(diag_y, fs))
                n_i = [effect([scale(conj(v[j]), fs[j]) for j in range(r)], w) for v, w in frame]
                for j, k in product(range(r), repeat=2):
                    assert csum(x[j][k] for x in n_i) == (fs[j]**2 if j == k else 0, 0)
                assert sum(spec[j]**2*fs[j]**2 for j in range(r)) == s
                values = [sum(x[j][j][0]*h[j] for j in range(r)) for x in m]
                correct = F(0)
                ratios = []
                for v, w in frame:
                    guessed = [scale(conj(v[j]), fs[j]) for j in range(r)]
                    signal = [scale(conj(v[j]), spec[j]) for j in range(r)]
                    overlap = dot(guessed, signal)
                    correct += w*w*mul(overlap, conj(overlap))[0]
                    ratios.append(w*sum(mul(z, conj(z))[0]/a for z, a in zip(signal, diag_d)))
                assert correct == base + sum((x-alpha)**2 for x in values)
                assert [x/alpha for x in values] == ratios
                if unequal:
                    assert correct > base and max(ratios) > 1
                    passed_strict += 1
                else:
                    assert all(z == 1 for z in ratios)
                    assert sum(diag_y)+mu*s == correct == base
                    passed_balanced += 1
                if n != d:
                    assert base != sum(h)**2/d  # wrong ambient denominator
                cases += 1

    # One exact nonflat duplicate-rate exception and a two-rate obstruction.
    root = [F(4, 5), F(3, 5)]
    uh = [F(4, 5), F(13, 20), F(3, 5), F(7, 20)]
    z = []
    for u in uh:
        hh = [min(x, u) for x in root]
        z.append(tuple(x/sum(hh) for x in hh))
    assert len(set(z)) == 3 and z[2] == z[3]
    assert (z[0][0]-z[2][0]) == F(1, 14)
    assert F(1)-2*root[1]**2 == F(7, 25)  # first support-flat rate

    g = [[(1,0),(0,0)], [(0,0),(1,0)], [(1,0),(1,0)], [(1,0),(0,1)]]
    rank_control = 0
    for t in [F(0), F(1), F(1, 2), F(1, 4), F(1, 16), F(1, 256)]:
        vectors = []
        for i, (f, _) in enumerate(fourier_frame(2)):
            vectors.append([add(scale(a,(1-t)/2), scale(b,t)) for a,b in zip(f,g[i])])
        coords = []
        for v in vectors:
            m = effect(v, F(1))
            coords.append([m[0][0][0],m[1][1][0],m[0][1][0],m[0][1][1]])
        assert (rational_det(coords) != 0) == (t not in (0, F(1, 2)))  # a second root on this path
        rank_control += 1

    print(f"exact PASS: {cases} rational complex frame/rate cases; {support_cases} singular-support cases")
    print(f"exact PASS: {passed_balanced} matching primal/dual checks; {passed_strict} strict-gap and failed-dual controls")
    print(f"exact PASS: endpoint/tie/plateau controls; {rank_control} exact MIC path determinants")


if __name__ == "__main__":
    check()
