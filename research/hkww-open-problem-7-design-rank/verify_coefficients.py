#!/usr/bin/env python3
"""Independent ANF coefficient rank certificate, without incidence matrices."""
from operator import xor
from functools import reduce

if not __debug__:
    raise RuntimeError("Run without -O")


def parity_set(items):
    support = set()
    for z in items:
        if z in support:
            support.remove(z)
        else:
            support.add(z)
    return support


def coordinate_anf(s):
    d = 2 * s
    X = [1 << j for j in range(d)]
    Y = [1 << (d + j) for j in range(d)]
    g = {x | y for x, y in zip(X, Y)}
    eps = set(Y)
    linear = set()
    for j in range(0, d, 2):
        a, b = Y[j:j+2]
        u, v = X[j:j+2]
        eps.add(a | b)
        # Binary multiplication by omega sends (a,b) -> (b,a+b).
        linear.update((u | b, v | a, v | b))
    h = linear ^ parity_set(u | v for u in g for v in eps)
    assert max(map(int.bit_count, h)) == 4
    return g, h


def toggle(matrix, row, col):
    if row not in matrix:
        matrix[row] = set()
    if col in matrix[row]:
        matrix[row].remove(col)
    else:
        matrix[row].add(col)


def translation_coefficients(h):
    out = {}
    # For each squarefree monomial, assign each variable to the row or
    # column side of the sum. This is a disjoint partition of its mask.
    for mask in h:
        left = mask
        while True:
            toggle(out, left, mask ^ left)
            if left == 0:
                break
            left = (left - 1) & mask
    return out


def column_elimination(row_sets):
    # Sparse coefficient matrix compression: only present monomials
    # occur. Work with columns as sets and least pivots, not truth rows.
    cols = {}
    for i, js in row_sets.items():
        for j in js:
            cols.setdefault(j, set()).add(i)
    basis = {}
    for x in cols.values():
        x = x.copy()
        while x:
            p = min(x)
            if p not in basis:
                basis[p] = x
                break
            x.symmetric_difference_update(basis[p])
    return len(basis)


def evaluate(support, z):
    return sum(z & mon == mon for mon in support) % 2


def binary_pair_map(y, s):
    blocks = [y >> (2*i) & 3 for i in range(s)]
    epsilon = sum(block != 0 for block in blocks) % 2
    rot = sum((0, 2, 3, 1)[block] << (2*i) for i, block in enumerate(blocks))
    return rot ^ (epsilon * y)


def check(s):
    d, m = 2 * s, 4 * s
    g, h = coordinate_anf(s)
    values = [binary_pair_map(y, s) for y in range(1 << d)]
    assert len(set(values)) == 1 << d
    for y, value in enumerate(values):
        assert values[value] == (value ^ y)
        D = reduce(xor, (values[y ^ (u << (2*i))]
                         for i in range(s) for u in range(4)), 0)
        assert D == y
        if y < 64:  # Compare the independent ANF and pair formulas.
            x = ((y * 277) ^ 63) & ((1 << d) - 1)
            z = x | (y << d)
            assert evaluate(h, z) == (x & value).bit_count() % 2
            assert evaluate(g, z) == (x & y).bit_count() % 2

    T = translation_coefficients(h)
    rank_T = column_elimination(T)
    for mon in g:
        toggle(T, mon, 0)
    for mon in g ^ h:
        toggle(T, 0, mon)
    rank_A = column_elimination(T)
    expected = 2 + 2*m + d*(d-1)
    assert (rank_A, rank_T) == (expected-1, expected)
    print(f"m={m}: polynomial-basis ranks (D,TD)=({rank_A},{rank_T}) PASS")


if __name__ == "__main__":
    for s in (2, 4, 6, 8):
        check(s)
    # Using one coordinate plane alone yields projection onto the other
    # plane, not all of y. This detects a missing shift block.
    partial = reduce(xor, (binary_pair_map(1 ^ u, 2) for u in range(4)), 0)
    assert partial != 1
    print("missing-plane negative control PASS")
