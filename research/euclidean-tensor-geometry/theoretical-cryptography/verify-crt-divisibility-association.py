#!/usr/bin/env python3
"""Exact rational checks of CRT divisibility association for two toy models."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from math import prod


def evalpoly(k, a, modulus):
    return sum(c * pow(a, j, modulus) for j, c in enumerate(k)) % modulus


# Each block is (cyclic residue size, image of the ring generator).
# The canonical coefficient dimension is d, not the number of blocks.
def idempotents(d, q, blocks):
    if d == 1:
        return [(q // m * pow(q // m, -1, m) % q,) for m, _ in blocks]
    assert d == len(blocks) and all(m == q for m, _ in blocks)
    out = []
    for _, a in blocks:
        poly, denom = [1], 1
        for _, b in blocks:
            if a == b:
                continue
            prev, poly = poly, [0] * (len(poly) + 1)
            for j, c in enumerate(prev):
                poly[j] -= b * c
                poly[j + 1] += c
            denom = denom * (a - b) % q
        out.append(tuple(c * pow(denom, -1, q) % q for c in poly))
    return out


def words(r):
    return range(1 << r)


def pattern(k, blocks):
    return sum((evalpoly(k, a, m) == 0) << i for i, (m, a) in enumerate(blocks))


def box(d, cutoff):
    return product(range(-cutoff, cutoff + 1), repeat=d)


def norm2(k):
    return sum(c * c for c in k)


def tail(z, d, cutoff):
    # A union over omitted coordinates, with each consecutive square
    # at least one increment apart. Bounds the primal and the dual sums.
    return d * 2 * z ** ((cutoff + 1)**2) / (1-z) * (1+2*z/(1-z))**(d-1)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def mulpos(a, b):
    assert min(a[0], b[0]) >= 0
    return a[0] * b[0], a[1] * b[1]


def mass(law, event):
    a = (F(0), F(0))
    for y in event:
        a = add(a, law[y])
    return a


def cov(law, A, B):
    return sub(mass(law, A & B), mulpos(mass(law, A), mass(law, B)))


def certified_mass(W, error, norm, norm_error):
    return (max(F(0), W-error)/(norm+norm_error),
            min(F(1), (W+error)/norm))


def primal(d, blocks, v, cutoff=2):
    out = {y: F(0) for y in words(len(blocks))}
    for k in box(d, cutoff):
        out[pattern(k, blocks)] += v**norm2(k)
    N, e = sum(out.values()), tail(v, d, cutoff)
    # Omitted primal masses are nonnegative.
    return {y: (w/(N+e), min(F(1), (w+e)/N)) for y, w in out.items()}


def dual(d, q, blocks, t, cutoff=2):
    r, E = len(blocks), idempotents(d, q, blocks)
    for i, e in enumerate(E):
        assert all(evalpoly(e, a, m) == (i == j) for j, (m, a) in enumerate(blocks))
    assert all(pow(a, d, m) == m-1 for m, a in blocks)
    # Each E_i generates the additive CRT block in these two examples.
    H = {(i, y): (F(1) if y & (1 << i) else F(-1, m-1))
         for i, (m, _) in enumerate(blocks) for y in words(r)}
    uniform = {y: prod(F(1 if y & (1 << i) else m-1, m)
                       for i, (m, _) in enumerate(blocks)) for y in words(r)}
    assert sum(uniform.values()) == 1
    out, shell = {y: F(0) for y in words(r)}, [0, 0]
    N = F(0)
    for k in box(d, cutoff):
        active = [i for i, e in enumerate(E) if sum(a*b for a, b in zip(k, e)) % q]
        n = norm2(k)
        if n in (1, 2):
            shell[n-1] += 1
            assert len(active) == r
        if not active:
            assert all(c % q == 0 for c in k)
            N += t**n
        for y in out:
            out[y] += t**n * prod(H[i, y] for i in active)
    assert shell == [2*d, 2*d*(d-1)]
    e = tail(t, d, cutoff)
    law = {y: certified_mass(uniform[y]*w, uniform[y]*e, N, e) for y, w in out.items()}
    assert sum(a[0] for a in law.values()) <= 1 <= sum(a[1] for a in law.values())
    a = 2*d*t + 2*d*(d-1)*t*t
    B = 800*d**3*t**3
    for y, bounds in law.items():
        relative_middle = 1+a*prod(H[i, y] for i in range(r))
        assert relative_middle-B <= bounds[0]/uniform[y] <= bounds[1]/uniform[y] <= relative_middle+B
    return law, len(law)


@lru_cache(None)
def upsets(r):
    ans = []
    for mask in range(1, (1 << (1 << r))-1):
        A = frozenset(y for y in words(r) if mask & (1 << y))
        if all((y | (1 << i)) in A for y in A for i in range(r)):
            ans.append(A)
    return tuple(ans)


def support_mask(indices, y):
    return sum(((y >> i) & 1) << j for j, i in enumerate(indices))


def lift(indices, A, r):
    return frozenset(y for y in words(r) if support_mask(indices, y) in A)


def top(indices, A):
    return sum((-1)**(len(indices)-x.bit_count()) for x in A)


def verify_case(d, q, blocks):
    r = len(blocks)
    assert prod(m for m, _ in blocks) == q**d
    v = F(1, 128)
    assert v <= F(1, 16*d)
    narrow = primal(d, blocks, v)
    narrow_ups = upsets(r)
    prob_narrow = {A: mass(narrow, A) for A in narrow_ups}
    count_narrow = 0
    for A, B in combinations_with_replacement(narrow_ups, 2):
        covariance = sub(prob_narrow[A & B], mulpos(prob_narrow[A], prob_narrow[B]))
        assert covariance[0] > 0
        count_narrow += 1

    # The certificate is checked both deep in the proven sufficient range
    # and at a broader t than that conservative uniform bound may cover.
    count_broad, count_cond, count_pattern = 0, 0, 0
    for t in (F(1, 2048), F(1, 128)):
        assert t <= F(1, 16*d)
        M1, M2 = blocks[0][0], blocks[1][0]
        if t == F(1, 2048):
            assert (60*d*t)**2 * (M1+M2-1) <= 1
        law, n = dual(d, q, blocks, t)
        count_pattern += n
        or01 = frozenset(y for y in words(r) if y & 3)
        tail_ones = frozenset(y for y in words(r) if y >> 2 == (1 << (r-2))-1)
        assert cov(law, or01, tail_ones)[1] < 0
        for k in range(1, r):
            for I in combinations(range(r), k):
                J = tuple(j for j in range(r) if j not in I)
                for u, v0 in product(upsets(k), upsets(r-k)):
                    orient = top(I, u)*top(J, v0)
                    if not orient:
                        continue
                    lower, upper = cov(law, lift(I, u, r), lift(J, v0, r))
                    assert lower > 0 if orient > 0 else upper < 0
                    count_broad += 1
        for i, j in combinations(range(r), 2):
            other = tuple(k for k in range(r) if k not in (i, j))
            for cut in words(len(other)):
                C = lift(other, {cut}, r)
                A = frozenset(y for y in C if y & (1 << i))
                B = frozenset(y for y in C if y & (1 << j))
                assert mass(law, C)[0] > 0
                score = sub(mulpos(mass(law, A & B), mass(law, C)),
                            mulpos(mass(law, A), mass(law, B)))
                sign = (-1)**(r-2-cut.bit_count())
                assert score[0] > 0 if sign > 0 else score[1] < 0
                count_cond += 1
    print(f"d={d}, q={q}: {count_pattern} pattern bounds, {count_narrow} narrow event pairs, "
          f"{count_broad} broad complementary signs, {count_cond} conditional signs")


if __name__ == "__main__":
    verify_case(4, 17, [(17, a) for a in (2, 8, 9, 15)])
    verify_case(1, 315, [(9, -1), (5, -1), (7, -1)])
    print("PASS")
