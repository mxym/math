#!/usr/bin/env python3
"""Exact all-tangent Hessian checks for orders 4..8 (integer-only)."""

from itertools import combinations
from math import comb


def derangements(n):
    if n == 0:
        return 1
    if n == 1:
        return 0
    a, b = 1, 0
    for m in range(2, n + 1):
        a, b = b, (m - 1) * (a + b)
    return b


def permanent01(rows):
    n = len(rows)
    dp = [0] * (1 << n)
    dp[0] = 1
    for mask in range(1, 1 << n):
        r = mask.bit_count() - 1
        dp[mask] = sum(rows[r][j] * dp[mask ^ (1 << j)]
                       for j in range(n) if mask & (1 << j))
    return dp[-1]


def rank_mod_p(vectors, p=1000000007):
    basis = {}
    for v in vectors:
        z = [u % p for u in v]
        while True:
            j = next((k for k, x in enumerate(z) if x != 0), None)
            if j is None:
                break
            if j not in basis:
                scale = pow(z[j], -1, p)
                basis[j] = [(x * scale) % p for x in z]
                break
            t = z[j]
            z = [(a - t * b) % p for a, b in zip(z, basis[j])]
    return len(basis)


def verify_order(n):
    coords = [(i, j) for i in range(n) for j in range(n) if i != j]
    index = {ij: k for k, ij in enumerate(coords)}
    m = len(coords)
    minors = [[0] * m for _ in range(m)]
    for a, (i, j) in enumerate(coords):
        for b, (k, l) in enumerate(coords):
            if i == k or j == l:
                continue
            rr = [r for r in range(n) if r not in (i, k)]
            cc = [c for c in range(n) if c not in (j, l)]
            minors[a][b] = permanent01([[int(r != c) for c in cc] for r in rr])
    assert all(minors[a][b] == minors[b][a] for a in range(m) for b in range(m))
    d0, d1, d2 = (derangements(n - 2),
                  derangements(n - 3), derangements(n - 4))
    coef_a = d0 + 2 * d1 + d2
    coef_b = d2
    lam_sym, lam_skew = coef_a + coef_b, coef_a - coef_b

    sym = []
    for a, b, c, d in combinations(range(n), 4):
        for edge_sets in [([(a,b),(c,d)], [(a,c),(b,d)]),
                          ([(a,b),(c,d)], [(a,d),(b,c)])]:
            x = [0] * m
            for edges, sign in zip(edge_sets, (1, -1)):
                for i, j in edges:
                    x[index[i, j]] += sign
                    x[index[j, i]] += sign
            sym.append(x)
    skew = []
    for a, b, c in combinations(range(n), 3):
        x = [0] * m
        for i, j in [(a, b), (b, c), (c, a)]:
            x[index[i, j]] += 1
            x[index[j, i]] -= 1
        skew.append(x)
    dim_sym, dim_skew = n * (n - 3) // 2, (n - 1) * (n - 2) // 2
    assert rank_mod_p(sym) == dim_sym
    assert rank_mod_p(skew) == dim_skew
    assert dim_sym + dim_skew == n * n - 3 * n + 1
    for sector, candidates, lam in [('symmetric', sym, lam_sym),
                                    ('skew', skew, lam_skew)]:
        for x in candidates:
            for i in range(n):
                assert sum(x[index[i, j]] for j in range(n) if i != j) == 0
                assert sum(x[index[j, i]] for j in range(n) if i != j) == 0
            for a in range(m):
                lhs = sum(minors[a][b] * x[b] for b in range(m))
                rhs = lam * x[a]
                if lhs != rhs:
                    raise AssertionError((n, sector, a, lhs, rhs))
    print(f'n={n}: PASS; dimensions {dim_sym}+{dim_skew}; '
          f'Hessian eigenvalues {lam_sym}/{(n-1)**(n-2)}, '
          f'{lam_skew}/{(n-1)**(n-2)}')


if __name__ == '__main__':
    for n in range(4, 9):
        verify_order(n)
