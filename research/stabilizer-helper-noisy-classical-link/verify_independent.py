#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations, product

def compositions(total, parts, prefix=()):
    if parts == 1:
        yield prefix + (total,)
        return
    for first in range(total + 1):
        yield from compositions(total - first, parts - 1,
                                prefix + (first,))

def coeff_N(W, N):
    X, Z = len(W), len(W[0])
    best = F(-1)
    for k in range(1, min(X, N) + 1):
        for S in combinations(range(X), k):
            value = sum(max(W[x][z] for x in S) for z in range(Z))
            best = max(best, value)
    return best

checks = 0
# Independent route: enumerate all half-grid stochastic encoders and verify
# that none beats a deterministic N-code.  This checks the convex-extreme
# step in the r=0 proof without calling the first verifier.
for X in range(1, 4):
    encoder_rows = [
        [F(v, 2) for v in c] for c in compositions(2, X)
    ]
    channel_rows = [
        [F(v, 2) for v in c] for c in compositions(2, 2)
    ]
    for N in range(1, 4):
        encoders = product(encoder_rows, repeat=N)
        encoder_list = list(encoders)
        for inds in product(range(len(channel_rows)), repeat=X):
            W = [channel_rows[i] for i in inds]
            best = F(-1)
            for E in encoder_list:
                value = sum(
                    max(sum(E[y][x] * W[x][z] for x in range(X))
                        for y in range(N))
                    for z in range(2)
                )
                best = max(best, value)
            assert best == coeff_N(W, N)
            checks += 1

# Independently check the elementary channel-coefficient bound
# C(W) <= min(number of input rows, number of output symbols).
for N in range(1, 6):
    for X in range(1, 4):
        channel_rows = [
            [F(v, 3) for v in c] for c in compositions(3, 3)
        ]
        for inds in product(range(len(channel_rows)), repeat=X):
            W = [channel_rows[i] for i in inds]
            alphas = [max(W[x][z] for x in range(X)) for z in range(3)]
            assert sum(alphas) <= F(X)
            assert sum(alphas) <= F(3)
            checks += 1

print(f"independent noisy-helper checks passed: {checks}")
