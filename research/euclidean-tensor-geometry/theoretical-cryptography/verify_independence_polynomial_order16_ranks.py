#!/usr/bin/env python3
"""Exact order-16 rank exclusions and connected fixed-rank witnesses."""
from itertools import combinations

from verify_independence_polynomial_order15_uniqueness import (
    clique_vector, colored_caps, envelope,
)


def partitions(n, bound, small=1):
    """Sorted positive parts, at most bound of them."""
    if n == 0:
        yield ()
    elif bound > 0:
        for a in range(small, n + 1):
            for tail in partitions(n - a, bound - 1, a):
                yield (a, *tail)


def multipartite_f(parts):
    f = [1] + [0] * 16
    for a in parts:
        for j in range(16, 0, -1):
            f[j] += a * f[j - 1]
    return f


def max_score(n, r, coeff):
    options = list(partitions(n, r))
    vals = [sum(w * f[k] for k, w in coeff.items())
            for f in map(multipartite_f, options)]
    return len(options), max(vals)


def full_edges(n):
    return set(combinations(range(n), 2))


def connected_complement(n, edges):
    E = full_edges(n) - edges
    S = {0}
    for _ in range(n - 1):
        for a, b in E:
            if a in S or b in S:
                S.update((a, b))
    return len(S) == n


def check_witness(n, edges, expected):
    assert clique_vector(n, edges, len(expected) + 1) == expected + [0, 0]
    assert connected_complement(n, edges)


def main():
    possible = {}
    for r in range(3, 17):
        raw = envelope(16, r)
        if raw:
            possible[r] = {pair for pairs in raw.values() for pair in pairs}
    assert set(possible) == {5, 6, 7, 8, 9, 11}
    assert {r: {k for k, a in v} for r, v in possible.items()} == {
        5:{2}, 6:{2,3}, 7:{3}, 8:{4}, 9:{4}, 11:{5},
    }
    assert {r: min(a for k,a in possible[r]) for r in (8,9,11)} == {
        8:220, 9:175, 11:637,
    }
    # Independent colored checks for the order-16 rise thresholds used.
    caps84 = colored_caps(16, 8)[4]
    assert min(a for a, x in enumerate(caps84) if x > a) == 220
    # Signed Zykov certificates. Maxima and all arithmetic are integers.
    assert max_score(16, 8, {3:7168,4:-2968,5:663}) == (186,1075200)
    assert max_score(7, 7, {2:1,3:1,4:-1}) == (15,30)
    n11, value11 = max_score(16, 11, {4:379,5:-236,6:62})
    assert (n11, value11) == (219, 117963)
    assert 4863 * 220 + 7831 > 1075200
    assert 205 * 637 + 441 > value11
    assert 126 + 7 + 1 + 21 < 175
    print('Integer certificates passed:', [(8,186), (9,15), (11,n11)])

    # All witnesses are specified by the edges in their complements.
    check_witness(16, full_edges(6) - {(0,1)}, [1,16,14,16,9,2])
    check_witness(16, full_edges(6), [1,16,15,20,15,6,1])

    left, right = range(7,11), range(11,16)
    E7 = full_edges(7) | {(u,v) for u in left for v in right}
    E7 |= {(i,7) for i in range(1,7)}
    E7 |= {(1,i) for i in range(8,11)} | {(0,j) for j in right}
    check_witness(16, E7, [1,16,55,50,55,36,13,2])

    left, right = range(8,12), range(12,17)
    E8 = full_edges(8) | {(u,v) for u in left for v in right}
    E8 |= {(0,i) for i in left} | {(1,j) for j in right}
    check_witness(17, E8, [1,17,57,56,70,56,28,8,1])
    print('Connected witnesses with independence numbers 5, 6, 7, 8 passed.')


if __name__ == '__main__':
    main()
