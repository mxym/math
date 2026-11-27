#!/usr/bin/env python3
"""Independent truth-table, subspace incidence, and rank-probability checks."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from random import Random


def restrict(x, base, columns):
    for i, b in enumerate(columns):
        if x & (1 << i):
            base ^= b
    return base


def values(table, base, columns):
    return [table[restrict(x, base, columns)] for x in range(1 << len(columns))]


def degree(table):
    n = len(table).bit_length() - 1
    a = list(table)
    for j in range(n):
        for i in range(len(a)):
            if i & (1 << j):
                a[i] ^= a[i ^ (1 << j)]
    return max((i.bit_count() for i, f in enumerate(a) if f), default=0)


def derivative2(table, a, b):
    return tuple(table[x] ^ table[x ^ a] ^ table[x ^ b] ^ table[x ^ a ^ b]
                 for x in range(len(table)))


def derivative3(table, a, b, c):
    g = derivative2(table, a, b)
    return tuple(y ^ g[x ^ c] for x, y in enumerate(g))


def anftable(n, coeff):
    return [sum_xor(b for a, b in coeff if a & x == a) for x in range(1 << n)]


def sum_xor(seq):
    out = 0
    for x in seq:
        out ^= x
    return out


rng = Random(20261127)
cnt = high = low = 0
for n in (4, 5, 6):
    f = anftable(n, [(a, rng.randrange(1 << 7)) for a in range(1 << n)
                     if a.bit_count() <= 3])
    assert degree(f) <= 3
    # Sample translates of coordinate subspaces of dimension three or four.
    for ids in combinations(range(n), min(n-1, 4)):
        cols = tuple(1 << i for i in ids)
        g = values(f, 0, cols)
        m = len(cols)
        for j in range(4):
            h = values(f, rng.randrange(1 << n), cols)
            assert all(len(set(derivative3(h, 1 << a, 1 << b, 1 << c))) == 1
                       for a, b, c in combinations(range(m), 3))
            assert (degree(h) <= 2) == all(derivative3(h, 1 << a, 1 << b, 1 << c)[0] == 0
                                          for a, b, c in combinations(range(m), 3))
            low += (degree(h) <= 2)
            for a, b in product(range(1 << m), repeat=2):
                p = Counter(derivative2(h, a, b))
                q = Counter(derivative2(g, a, b))
                assert len(p) == len(q) and len(p) & (len(p)-1) == 0
                assert min(p.values()) == max(p.values())
                if a == b or not a or not b:
                    assert p == {0: len(h)}
                cnt += 1
                high += (len(p) >= 4)
# Degree really drops on both translates of a pivot-free direction space.
lo = anftable(5, [(0b00111, 1), (0b11001, 2), (0b00010, 4)])
assert degree(lo) == 3  # Negative control: the ambient map is not quadratic.
for pivot in (0, 1):
    h = values(lo, pivot, (2, 4, 8, 16))
    assert degree(h) == (2 if pivot else 1)
    low += 1
print(f"truth-table restriction/derivatives: {cnt} PASS; {high} rank>=2; {low} quadratic cosets")

# All 2-planes in a fixed four-space, enumerated without a rank oracle.
n = 4
planes = sorted({tuple(sorted((0, a, b, a ^ b))) for a in range(1, 1 << n)
                 for b in range(1, 1 << n) if a != b})
assert len(planes) == 35
for v in range(1, 1 << n):
    assert F(sum(v in p for p in planes), len(planes)) == F(3, 15)


def cosets(p):
    return {tuple(sorted(x ^ a for a in p)) for x in range(1 << n)}


for mod in (1, 2, 3):
    points = tuple(range(1 << n))
    # Explicit finite maps with collisions, not assumed cubic for this
    # probabilistic step. The bound is valid for arbitrary maps.
    f = tuple((x % (5+mod)) ^ (x//(5+mod) % 2 if mod == 3 else 0) for x in points)
    k_inverse = F(max(Counter(f).values()), len(points))
    average = F(0)
    for w in planes:
        bad = {x for cell in cosets(w) for x in cell
               if any(x != y and f[x] == f[y] for y in cell)}
        average += F(len(bad), (1 << n)*len(planes))
        for d in w[1:]:
            bad_cosets = sum(any(x != y and f[x] == f[y] for x,y in product(c, repeat=2))
                             for c in cosets((0, d)))
            assert bad_cosets <= len(bad)
    assert average <= 4*k_inverse
print("random-plane incidence and refined-coset collision bound: 35 planes, 3 maps PASS")

# Exact rank law of a sequence of uniformly random columns; independent of
# the proof's spanning-index union bound. Check the asymptotic inequalities
# at and above the stated m=16 threshold by exact rational arithmetic.
for m in range(16, 45):
    r, s = m, m//2
    law = {0: F(1)}
    for _ in range(m-2):
        nxt = Counter()
        for i, p in law.items():
            same = F(1 << i, 1 << r)
            nxt[i] += p*same
            nxt[i+1] += p*(1-same)
        law = nxt
    fail = sum(law.get(i, F(0)) for i in range(s))
    union = comb(m-2, s-1)*F(1, 1 << ((r-s+1)*(m-s-1)))
    assert fail <= union <= F(1, 1 << (3*m+1))
    assert F(1, 1 << (m+4)) + F(1, 8) + (1 << (2*m))*union < 1
print("exact random-column rank law and total failure budget: m=16..44 PASS")

# The dyadic cutoff and the even-rounding boundary, including m=16.
used = set(range(16, 513))
for e in range(4, 17):
    used.update(m for m in (2**e-1, 2**e, 2**e+1) if m >= 16)
for m in sorted(used):
    j = (m.bit_length()-1)//4
    a = 2*m+5
    h = 2+2*((a+2*j-1)//(2*j))
    B = 2*(1 << (2*j))*(2*m+4)
    L = 2*m+4+m*(B+1)+h*(m-1)*comb(m,2)
    assert j >= 1 and (1 << (4*j)) <= m < (1 << (4*j+4))
    assert h % 2 == 0 and j*(h-4) < a <= j*(h-2)
    assert (h-1)*j >= a+j
    summed = h*(m-1)*(m-1)*m//2+m*(B+1)
    assert L-summed == 2*m+4
    assert L*(m-1).bit_length() <= 16*m**4
print(f"even-fold exponent, dyadic jumps, and explicit dimension budget: {len(used)} cases PASS")
