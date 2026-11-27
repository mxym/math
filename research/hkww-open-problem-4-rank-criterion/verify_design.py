#!/usr/bin/env python3
"""Direct truth-table and incidence tests of HKWW OP4 examples."""

from functools import reduce
from itertools import combinations
from operator import xor

if not __debug__:
    raise RuntimeError("Run without -O")


def parity(a):
    return a.bit_count() & 1


def mod2_rank(rows):
    rows = list(rows)
    r = 0
    while r < len(rows):
        j = max(range(r, len(rows)), key=rows.__getitem__)
        p = rows[j]
        if not p:
            break
        rows[r], rows[j] = p, rows[r]
        mask = 1 << (p.bit_length()-1)
        for i in range(r+1, len(rows)):
            if rows[i] & mask:
                rows[i] ^= p
        r += 1
    return r


def addition_blocks(f):
    N = len(f)
    u = 1 << ((N.bit_length()-1)//2)
    table = sum(bo << a for a, bo in enumerate(f))
    result = []
    for a in range(N):
        linear = sum(parity(a & z) << z for z in range(N))
        cut = table ^ linear
        w = N-2*cut.bit_count()
        assert abs(w) == u
        result.append(cut if w > 0 else cut ^ ((1 << N)-1))
    return result


def add_design_union(functions, n, r, expect_tsdp):
    assert len(functions) == 1 << r
    v = 1 << (2*n)
    k = (v - (1 << n))//2
    target_lambda = (1 << r)*(v//4 - (1 << (n-1)))
    groups = list(map(addition_blocks, functions))
    masks = [b for group in groups for b in group]
    b = len(masks)
    assert b == 1 << (2*n+r)
    assert len(set(masks)) == b
    assert {x.bit_count() for x in masks} == {k}
    rows = [sum((block >> i & 1) << j for j, block in enumerate(masks))
            for i in range(v)]
    assert {x.bit_count() for x in rows} == {(1 << r)*k}
    assert {(a & b).bit_count() for a, b in combinations(rows, 2)} == {target_lambda}
    assert mod2_rank(rows) == 2*n+r+2
    assert mod2_rank(masks) == 2*n+r+2

    J = (1 << v)-1
    allowed = set(masks) | {block ^ J for block in masks}
    # The normalized family modulo complements is affine iff it is
    # closed under triples; using one fixed block suffices to test this.
    assert expect_tsdp == all(
        (a ^ c ^ masks[0]) in allowed for a, c in combinations(masks, 2)
    )
    # Check all-one membership in the point-row code, not block code.
    expected_rank_with_ones = 2*n+r+2+(not expect_tsdp)
    assert mod2_rank(rows+[(1 << b)-1]) == expected_rank_with_ones
    return groups, (v, k, target_lambda)


def small():
    def values(fun):
        return [fun(*[(z >> j) & 1 for j in range(4)]) for z in range(16)]

    q1 = values(lambda x1, x2, y1, y2: (x1 & y1) ^ (x2 & y2))
    q2 = values(lambda x1, x2, y1, y2: (x1 & y2) ^ (x2 & (y1 ^ y2)))
    q3 = values(lambda x1, x2, y1, y2: (x1 & y2) ^ (x2 & y1))
    q12 = list(map(xor, q1, q2))
    groups, params = add_design_union([q1, q2, q12, q3], 2, 2, False)
    assert params == (16, 6, 8)
    assert reduce(xor, (group[0] for group in groups[:3])) == 0
    print("m=6,r=2: simple 2-(16,6,8), 64 blocks, rank 8, no TSDP PASS")
    _, params = add_design_union([q1, q2], 2, 1, True)
    assert params == (16, 6, 4)
    print("m=5,r=1: simple 2-(16,6,4), 32 blocks, rank 7, TSDP PASS")


def f8(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 8:
            a ^= 0b1011  # t^3+t+1
        b >>= 1
    return result


def larger():
    def vals(c):
        return [parity((z & 7) & f8(c, z >> 3)) for z in range(64)]

    for labels, pos in [((5, 6, 7, 1), False), ((4, 5, 6, 7), True)]:
        _, params = add_design_union(list(map(vals, labels)), 3, 2, pos)
        assert params == (64, 28, 48)
    print("m=8,r=2: F_8 perturbed and unperturbed affine label sets PASS")


if __name__ == "__main__":
    small()
    larger()
