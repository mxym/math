#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations, product

def subsets(n, N):
    for k in range(1, min(n, N) + 1):
        yield from combinations(range(n), k)

def coeff(W):
    return sum(max(W[x][z] for x in range(len(W)))
               for z in range(len(W[0])))

def coeff_N(W, N):
    return max(sum(max(W[x][z] for x in S)
                   for z in range(len(W[0])))
               for S in subsets(len(W), N))

rows = []
for a in range(4):
    for b in range(4 - a):
        rows.append((F(a, 3), F(b, 3), F(3 - a - b, 3)))

checks = 0
for X in range(1, 5):
    for inds in product(range(len(rows)), repeat=X):
        W = [rows[i] for i in inds]
        for N in range(1, 5):
            c, cn = coeff(W), coeff_N(W, N)
            assert F(1) <= cn <= min(c, F(N))
            checks += 1

for N in range(2, 8):
    for num in range(11):
        eta = F(num, 10)
        erasure = [
            [(1 - eta if z == x else F(0)) for z in range(N)] + [eta]
            for x in range(N)
        ]
        assert coeff_N(erasure, N) == N * (1 - eta) + eta
        symmetric = [
            [(1 - eta if z == x else eta / F(N - 1))
             for z in range(N)]
            for x in range(N)
        ]
        assert coeff_N(symmetric, N) == (
            N * max(1 - eta, eta / F(N - 1))
        )
        checks += 2

print(f"exact noisy-helper checks passed: {checks}")
