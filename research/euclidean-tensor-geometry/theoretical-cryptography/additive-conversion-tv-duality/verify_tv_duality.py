#!/usr/bin/env python3
"""Exact rational checks for translation-hull TV duality examples."""

from fractions import Fraction as F
from itertools import product


def translate(p, y):
    n = len(p)
    return tuple(p[(x - y) % n] for x in range(n))


def convolve(p, k):
    n = len(p)
    return tuple(sum(k[y] * p[(x - y) % n] for y in range(n))
                 for x in range(n))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def tv(a, b):
    return sum(abs(x - y) for x, y in zip(a, b)) / 2


def invert_average(v):
    n = len(v)
    return tuple((v[x] + v[(-x) % n]) / 2 for x in range(n))


def matrix_rank_fraction(rows):
    a = [list(row) for row in rows]
    m, n = len(a), len(a[0])
    rank = 0
    for col in range(n):
        pivot = next((r for r in range(rank, m) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        z = a[rank][col]
        a[rank] = [x / z for x in a[rank]]
        for r in range(m):
            if r != rank and a[r][col]:
                z = a[r][col]
                a[r] = [x - z * y for x, y in zip(a[r], a[rank])]
        rank += 1
    return rank


def circulant_columns(p):
    return tuple(translate(p, y) for y in range(len(p)))


def main():
    # Exact Z/5 symmetric primal-dual certificate.
    mu = (F(1, 3), F(1, 3), F(0), F(0), F(1, 3))
    nu = (F(1, 2), F(1, 4), F(0), F(0), F(1, 4))
    identity = (F(1), F(0), F(0), F(0), F(0))
    witness = (F(1), F(-1), F(-1), F(-1), F(-1))

    q = convolve(mu, identity)
    primal = tv(q, nu)
    translate_scores = tuple(dot(witness, translate(mu, y))
                             for y in range(5))
    dual = (dot(witness, nu) - max(translate_scores)) / 2

    assert primal == F(1, 6)
    assert dual == F(1, 6)
    assert primal == dual
    assert invert_average(mu) == mu
    assert invert_average(nu) == nu
    assert invert_average(witness) == witness

    # Symmetrizing an arbitrary converter cannot worsen this invariant problem.
    k = (F(1, 10), F(2, 10), F(3, 10), F(1, 10), F(3, 10))
    kbar = invert_average(k)
    assert sum(k) == sum(kbar) == 1
    assert invert_average(kbar) == kbar
    assert tv(convolve(mu, kbar), nu) <= tv(convolve(mu, k), nu)

    # Check the dual inequality against a rational grid of all bounded witnesses.
    # This is supplementary; equality above is already an exact proof.
    values = (F(-1), F(0), F(1))
    for f in product(values, repeat=5):
        value = (dot(f, nu) -
                 max(dot(f, translate(mu, y)) for y in range(5))) / 2
        assert value <= primal

    # Z/6 rank-three example: mu is uniform on the order-two subgroup.
    mu6 = (F(1, 2), F(0), F(0), F(1, 2), F(0), F(0))
    columns = circulant_columns(mu6)
    # Convert columns to row-major matrix for exact Gaussian elimination.
    rows = tuple(tuple(columns[col][row] for col in range(6))
                 for row in range(6))
    rank = matrix_rank_fraction(rows)
    assert rank == 3

    sparse_k = (F(1, 3), F(2, 3), F(0), F(0), F(0), F(0))
    target6 = convolve(mu6, sparse_k)
    assert sum(1 for x in sparse_k if x) == 2 <= rank
    assert target6 == (F(1, 6), F(1, 3), F(0),
                       F(1, 6), F(1, 3), F(0))

    print({
        "z5_optimal_tv": str(primal),
        "z5_dual_value": str(dual),
        "z5_translate_scores": [str(x) for x in translate_scores],
        "z5_symmetry_orbits": 3,
        "z6_convolution_rank": rank,
        "z6_converter_support": 2,
        "status": "PASS",
    })


if __name__ == "__main__":
    main()
