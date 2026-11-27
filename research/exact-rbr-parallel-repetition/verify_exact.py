#!/usr/bin/env python3
"""Rational dynamic programming on cutoff profiles, with no protocol implementation."""
from fractions import Fraction as F
from itertools import product
from math import comb


def probability_of_loss(a, b, p):
    return sum((comb(a, j) * p**j * (1-p)**(a-j)
                for j in range(a-b+1, a+1)), F(0))


def estimate(copies, probabilities):
    best = [F(0)] * (copies+1)
    for p in reversed(probabilities):
        best = [F(1)] + [min(max(probability_of_loss(a, b, p), best[b])
                                for b in range(1, a+1))
                         for a in range(1, copies+1)]
    return best[copies]


def quantiles(copies, probabilities, error):
    cutoff = 1
    for p in reversed(probabilities):
        cutoff = next((a for a in range(cutoff, copies+1)
                       if probability_of_loss(a, cutoff, p) <= error), copies+1)
    return cutoff <= copies


def main():
    p = F(1, 8)
    target = p**3
    first = probability_of_loss(6, 3, p)
    opt = estimate(6, (p, p))
    assert first == opt == F(389, 131072) and first > target
    assert (1-(1-p)**2) == F(15, 64) < F(1, 3)
    assert not quantiles(6, (p, p), target) and quantiles(6, (p, p), opt)
    print(f'two-challenge finite example: optimum {opt} > {target}; ordinary error 15/64')
    for L in range(3, 13):
        p = F(1, 2**L)
        k = 2*L
        assert probability_of_loss(2*k, k, p) > p**k
        assert not quantiles(2*k, (p, p), p**k)
    print('vanishing base error: exact obstruction for L=3..12, k=2L')
    profile_count = 0
    for r in range(1, 4):
        for profile in product((F(0), F(1, 8), F(1, 4), F(1, 2), F(1)), repeat=r):
            for m in range(1, 8):
                o = estimate(m, profile)
                assert quantiles(m, profile, o)
                if o > 0:
                    assert not quantiles(m, profile, o-F(1, 2*o.denominator**2))
                if m == 1:
                    assert o == max(profile)
                if r == 1:
                    assert o == profile[0]**m
                if 1 in profile:
                    assert o == 1
                profile_count += 1
    print(f'{profile_count} exact profile checks; all tie, zero, unit, and one-round boundaries')
    equality_count = 0
    for r in range(2, 6):
        for k in range(1, 6):
            m = r*k
            p = F(1, comb(m, k+1))
            assert estimate(m, (p,)*r) == p**k
            equality_count += 1
    print(f'{equality_count} exact small-p equality at the sufficient threshold')
    print('PASS rational minimax and cutoff feasibility')


if __name__ == '__main__':
    main()
