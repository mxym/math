#!/usr/bin/env python3
"""Packed binary ranks, exact failure bounds, rational shell moments."""
from fractions import Fraction as F
from itertools import combinations
from math import prod
from random import Random


def rank(rows):
    piv = {}
    for row in rows:
        while row:
            i = row.bit_length() - 1
            if i not in piv:
                piv[i] = row
                break
            row ^= piv[i]
    return len(piv)


def csets(n, t):
    for r in range(t + 1):
        yield from combinations(range(1, n + 1), r)


def condition(n, C, maps, widths):
    # M_d and B are realized directly as the setup / observed cut row vectors.
    J = sorted({j for i in C for j in (i - 1, i) if 0 < j < n})
    jpos = {cut: bit for bit, cut in enumerate(J)}
    B = [sum(1 << jpos[j] for j in (i - 1, i) if j in jpos) for i in C]
    honest = [d for d in range(len(maps)) if d + 1 not in C]
    local = []
    aggregate = [0] * len(J)
    off = 0
    for d in honest:
        a = maps[d]
        local.extend((a[i - 1] ^ a[i]) << off for i in C)
        for b, j in enumerate(J):
            aggregate[b] ^= a[j] << off
        off += widths[d]
    return rank(local + aggregate) - rank(local) == len(J) - rank(B)


def xor_field(a, b, pol):
    out = 0
    boundary = 1 << (pol.bit_length() - 1)
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & boundary:
            a ^= pol
    return out


def pow_field(a, exponent, pol):
    v = 1
    for _ in range(exponent):
        v = xor_field(v, a, pol)
    return v


def bch(n, t, pol):
    L = (n - 1).bit_length()
    assert pol.bit_length() == L + 1
    return [0] + [sum(pow_field(j, 2 * i + 1, pol) << (i * L)
                       for i in range(t)) for j in range(1, n)] + [0]


def main():
    poly = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101}
    bc_count = 0
    for n, t in ((2, 1), (4, 1), (5, 2), (8, 2), (12, 3), (17, 3), (24, 3)):
        L = (n - 1).bit_length()
        a = bch(n, t, poly[L])
        for C in csets(n, t):
            assert condition(n, C, [a] * (t + 1), [t * L] * (t + 1))
            bc_count += 1

    rng = Random(20261127)
    compact_count = 0
    cases = ((5, 2, 2), (8, 2, 4), (16, 2, 6), (21, 3, 10), (23, 3, 10))
    for n, t, r in cases:
        for D in (t, t + 1):
            p = min(D, n - 1)
            cohorts = tuple(csets(n, t))
            for _ in range(50):
                mats = [[0] + [1 << i for i in range(p)] +
                        [rng.getrandbits(r) << p for _ in range(n - p - 1)] + [0]
                        for _ in range(D)]
                if all(condition(n, C, mats, [p + r] * D) for C in cohorts):
                    compact_count += len(cohorts)
                    break
            else:
                raise AssertionError((n, t, r, D))

    # Aggregate cut rows span all visible cuts in this control, but their
    # per-dealer setup rows remove all admissible variation for C=(5,7).
    ctrl = [[0,1,2,4,8,0,16,0,0], [0,1,2,4,0,8,0,0,0],
            [0,1,2,4,0,0,0,8,0]]
    assert not condition(8, (5, 7), ctrl, [5,4,4])
    print(f"rank PASS: {bc_count} explicit BCH and {compact_count} compact matrix coalition tests; setup-aware control")

    ub_count = 0
    for n in tuple(range(2, 49)) + (64, 127, 128, 257, 1000, 1024, 1025):
        L = (n - 1).bit_length()
        for t in range(1, min(n, 42)):
            r = 4*t + L + 3
            for D in (t + 1, t):
                total = F(0)
                for k in range(t + 1):
                    if D == t and k == 0:
                        continue
                    h_min = D - t + k
                    total += F((1 << (D + 2*t)) * n**k, 1 << (h_min*(r-k)))
                assert total < 1
                ub_count += 1
    print(f"rank PASS: {ub_count} exact union-bound positivity checks, both dealer counts")

    moment_count = 0
    for k in range(1, 41):
        zs = [0, 1] + [2*j**4 for j in range(1, k+1)]
        ws = [F(1, prod(z - u for u in zs if z != u)) for z in zs]
        assert sum(ws) == 0
        for deg in range(k+2):
            assert sum(w*z**deg for w,z in zip(ws,zs)) == (deg == k+1)
            moment_count += 1
        L = sum(w for w in ws if w>0)
        assert L == sum(-w for w in ws if w<0)
        assert sum(abs(w)*z for w,z in zip(ws,zs)) <= 12*L
        assert abs(ws[1]/ws[0]) < 4
        for j in range(1,k+1):
            assert abs(ws[j+1]/ws[0]) * (zs[j+1]-1) <= F(4, 2**j)
    print(f"rational PASS: {moment_count} signed moments and all 40 expected-weight bounds")


if __name__ == "__main__":
    main()
