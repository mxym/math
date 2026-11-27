#!/usr/bin/env python3
"""Exact finite checks for the sparse Hall-Mahler module-generation note."""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import prod


def subsets(n):
    for k in range(n+1):
        yield from combinations(range(n), k)


def neighbors(L, S):
    return {j for i in S for j, c in enumerate(L[i]) if c}


def square_matchings(L):
    return sum(prod(L[i][j] for i, j in enumerate(p))
               for p in permutations(range(len(L))))


def rect_matching(L):
    return any(all(L[i][j] for i, j in enumerate(p))
               for p in permutations(range(len(L[0])), len(L)))


def restrict(L, rows, cols):
    return tuple(tuple(L[i][j] for j in cols) for i in rows)


def rank_mod(L, p):
    if not L or not L[0]:
        return 0
    A = [list(map(lambda z: z % p, row)) for row in L]
    rank = 0
    for j in range(len(A[0])):
        k = next((i for i in range(rank, len(A)) if A[i][j]), None)
        if k is None:
            continue
        A[rank], A[k] = A[k], A[rank]
        v = pow(A[rank][j], -1, p)
        A[rank] = [u*v % p for u in A[rank]]
        for i in range(rank+1, len(A)):
            c = A[i][j]
            A[i] = [(a-c*b) % p for a, b in zip(A[i], A[rank])]
        rank += 1
        if rank == len(A):
            break
    return rank


def split(L):
    r, m = len(L), len(L[0])
    if any(len(neighbors(L, S)) < len(S) for S in subsets(r)):
        return None
    S = sorted({i for T in subsets(r) if len(neighbors(L, T)) == len(T) for i in T})
    T = sorted(neighbors(L, S))
    return S, T, [i for i in range(r) if i not in S], [j for j in range(m) if j not in T]


def good(L):
    blocks = split(L)
    if blocks is None:
        return False
    S, T, U, V = blocks
    return square_matchings(restrict(L, S, T)) == 1 and rank_mod(restrict(L, U, V), 2) == len(U)


def reshape(a, r, m):
    return tuple(tuple(a[i*m:(i+1)*m]) for i in range(r))


def check_hall():
    count = 0
    for r in range(1, 4):
        for m in range(1, 5):
            for a in product(range(2), repeat=r*m):
                L = reshape(a, r, m)
                blocks = split(L)
                assert (blocks is not None) == rect_matching(L)
                if blocks is not None:
                    S, T, U, V = blocks
                    assert len(S) == len(T)
                    assert all(not L[i][j] for i in S for j in V)
                    assert any(square_matchings(restrict(L, S, T)) == c
                               for c in range(1, 7))
                    for I in subsets(len(U)):
                        if I:
                            J = [U[i] for i in I]
                            assert len(neighbors(L, J) - set(T)) >= len(I)+1
                count += 1
    return count


def permutation_sign(p):
    return (-1)**sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p)))


def det_support(L, I=None, J=None):
    if I is None:
        I = J = tuple(range(len(L)))
    out = {}
    for perm in permutations(range(len(J))):
        edges = [(i, J[perm[k]]) for k, i in enumerate(I)]
        for choices in product(*(range(L[i][j]) for i, j in edges)):
            monomial = frozenset((i, j, h) for (i, j), h in zip(edges, choices))
            assert monomial not in out
            out[monomial] = permutation_sign(perm)
    return out


def components(active):
    todo = set(active)
    while todo:
        u = {next(iter(todo))}
        while True:
            rows = {i for i, _, _ in u}
            cols = {j for _, j, _ in u}
            new = {(i, j, h) for i, j, h in todo if i in rows or j in cols}
            if u == new:
                break
            u = new
        yield u, sorted(rows), sorted(cols)
        todo -= u


def check_components(L):
    P = det_support(L)
    assert len(P) == square_matchings(L)
    assert (sum(P.values()) % 2 != 0) == (rank_mod(L, 2) == len(L))
    if not P:
        return 0
    active = set().union(*P)
    full = {frozenset(): 1}
    n = 0
    for allowed, I, J in components(active):
        assert len(I) == len(J)
        Q = det_support(L, I, J)
        assert set().union(*Q) == allowed
        if len(allowed) == 1:
            assert len(Q) == 1
        else:
            assert not set.intersection(*(set(m) for m in Q))
            reciprocal = {frozenset(allowed - m) for m in Q} == set(Q)
            is_cycle = (all(sum(a == i for a, b, c in allowed) == 2 for i in I)
                        and all(sum(b == j for a, b, c in allowed) == 2 for j in J))
            assert reciprocal == is_cycle
            if is_cycle:
                assert len(Q) == 2
            else:
                assert len(Q) >= 3
        full = {a | b: v*w for a, v in full.items() for b, w in Q.items()}
        n += 1
    assert set(P) == set(full)
    assert len({P[a]*full[a] for a in P}) == 1
    return n


def det_integer(A):
    return sum(permutation_sign(p)*prod(A[i][j] for i, j in enumerate(p))
               for p in permutations(range(len(A))))


def check_anchor_examples():
    count = 0
    for zero_pattern in (
        ((1, 1, 1), (1, 1, 1)),
        ((1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 1, 1)),
        ((1, 1, 1, 0), (1, 0, 1, 1), (0, 1, 1, 1)),
    ):
        r, m = len(zero_pattern), len(zero_pattern[0])
        active = [(i, j) for i in range(r) for j in range(m) if zero_pattern[i][j]]
        for a in product(range(3), repeat=len(active)):
            A = [[0]*m for _ in range(r)]
            for (i, j), val in zip(active, a):
                A[i][j] = val
            if rank_mod(A, 3) == r:
                continue
            S = next(S for S in subsets(r) if rank_mod(restrict(A, S, range(m)), 3) < len(S))
            k = len(S)
            J = next(J for J in combinations(sorted(neighbors(zero_pattern, S)), k-1)
                     if rank_mod(restrict(A, S, J), 3) == k-1)
            c = [(-1)**i*det_integer(restrict(A, S[:i]+S[i+1:], J)) % 3 for i in range(k)]
            assert all(c)
            E = sorted(neighbors(zero_pattern, S) - set(J))
            assert len(E) >= 2
            assert all(sum(ci*A[ri][j] for ci, ri in zip(c, S)) % 3 == 0 for j in E)
            count += 1
    return count


def bareiss(A):
    A = [list(row) for row in A]
    n, sign, old = len(A), 1, 1
    if not n:
        return 1
    for j in range(n-1):
        k = next((i for i in range(j, n) if A[i][j]), None)
        if k is None:
            return 0
        if k != j:
            A[j], A[k] = A[k], A[j]
            sign = -sign
        p = A[j][j]
        for i in range(j+1, n):
            for k in range(j+1, n):
                val = A[i][k]*p - A[i][j]*A[j][k]
                val, rem = divmod(val, old)
                assert not rem
                A[i][k] = val
        old = p
    return sign*A[-1][-1]


def norm(n, terms):
    A = [[0]*n for _ in range(n)]
    for a in terms:
        for i in range(n):
            sign, j = divmod(a+i, n)
            A[j][i] += (-1)**sign
    return abs(bareiss(A))


def check_norms():
    count = 0
    for n in (2, 4, 8, 16):
        assert all(norm(n, [j]) == 1 for j in range(2*n))
        for k in range(1, 2*n):
            d = norm(n, [0, k])
            assert (d == 0) == (k == n)
            assert d == 0 or (d >= 2 and not d & (d-1))
            count += 1
    # An odd matching count is not enough even for a square rank-one
    # bottleneck. These formal genericity checks do not prove the Haar limit.
    assert norm(8, [0, 1, 3]) == 17
    return count


def check_formula():
    count = 0
    for weights in ((1, 2, 4, 3), (7, 1, 2, 0)):
        p = [Fraction(x, sum(weights)) for x in weights]
        a = p[1]+p[3]
        for m in range(1, 7):
            actual = sum(prod(p[c] for c in L) for L in product(range(4), repeat=m) if good((L,)))
            predicted = 1-(1-a)**m-m*p[0]**(m-1)*(a-p[1])
            assert actual == predicted
            count += 1
        actual = sum(prod(p[c] for c in s) for s in product(range(4), repeat=4) if good(reshape(s, 2, 2)))
        assert actual == 2*p[1]**2*(2*p[0]-p[0]**2)
        count += 1
    return count


if __name__ == "__main__":
    H = check_hall()
    R = check_anchor_examples()
    C = 0
    for r, colors in ((1, 5), (2, 4), (3, 3)):
        for s in product(range(colors), repeat=r*r):
            C += check_components(reshape(s, r, r))
    N = check_norms()
    F = check_formula()
    print(f"PASS: {H} Hall patterns, {R} deficient anchor instances, "
          f"{C} component checks, {N} exact norms, {F} probability identities")
