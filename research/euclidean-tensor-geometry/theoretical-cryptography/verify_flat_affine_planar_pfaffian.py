#!/usr/bin/env python3
"""Exact small Pfaffian/tree/phase checks, not a network testing tool.

Requires Python 3 and SymPy for the separate lattice-closure check.
Generated input only. No floating-point approximation to roots is used:
Gaussian integers remain in exact binary64 integer range in these tiny tests.
"""

from functools import lru_cache
from itertools import combinations, product
from math import factorial
from random import Random

from sympy import Matrix, eye
from sympy.matrices.normalforms import hermite_normal_form

U = (1, 1j, -1, -1j)
R = Random(908616)


def pfaffian(A, S):
    S = tuple(S)

    @lru_cache(None)
    def go(Q):
        if not Q:
            return 1
        return sum(
            (-1) ** (j + 1) * A[Q[0], Q[j]] * go(Q[1:j] + Q[j+1:])
            for j in range(1, len(Q))
        )

    return go(S)


def norm_one(z):
    return z.real**2 + z.imag**2 == 1


def has_module(A, S):
    return any(
        all(all(A[i, j] == A[J[0], j] for i in J) for j in S if j not in J)
        for k in range(2, len(S)) for J in combinations(S, k)
    )


def tree_from(A, S):
    if len(S) == 1:
        return S[0]
    # Deliberately use all bipartitions, not the closure algorithm in the note.
    for L in range(1, 2**len(S)-1):
        l = tuple(i for j, i in enumerate(S) if (L >> j) & 1)
        r = tuple(i for j, i in enumerate(S) if not ((L >> j) & 1))
        z = A[l[0], r[0]]
        if any(A[i, j] != z for i in l for j in r):
            continue
        lt, rt = tree_from(A, l), tree_from(A, r)
        if lt is not None and rt is not None:
            return (z, lt, rt)
    return None


def leaves(T):
    if isinstance(T, int):
        return [T]
    _, L, Rr = T
    return leaves(L) + leaves(Rr)


def parity_value(T, S):
    if isinstance(T, int):
        return int(T in S), 1
    z, L, Rr = T
    p, a = parity_value(L, S)
    q, b = parity_value(Rr, S)
    return p ^ q, a*b*(z if p and q else 1)


def sign_in_order(S, order):
    ptr = {v: j for j, v in enumerate(order)}
    return (-1)**sum(ptr[i] > ptr[j] for i, j in combinations(sorted(S), 2))


def random_tree(V):
    if len(V) == 1:
        return V[0]
    cut = R.randrange(1, len(V))
    return (R.choice(U), random_tree(V[:cut]), random_tree(V[cut:]))


def fill(T, A):
    if isinstance(T, int):
        return
    z, L, Rr = T
    for i, j in product(leaves(L), leaves(Rr)):
        A[i, j], A[j, i] = z, -z
    fill(L, A)
    fill(Rr, A)


def even_subsets(V):
    return (S for h in range(0, len(V)+1, 2) for S in combinations(V, h))


def chart_case(A, V):
    p, others = V[0], tuple(V[1:])
    T = tree_from(A, others)
    small = all(has_module(A, S) for h in (3, 4) for S in combinations(others, h))
    flat4 = all(norm_one(pfaffian(A, S)) for S in combinations(V, 4))
    assert (T is not None) == small == flat4
    checked = 0
    if T is not None:
        T = (1, p, T)
        for S in even_subsets(V):
            parity, z = parity_value(T, set(S))
            assert parity == 0 and norm_one(z)
            assert pfaffian(A, S) == sign_in_order(S, leaves(T))*z
            checked += 1
    return int(T is not None), checked


charts = flat_charts = chart_values = 0
for n in range(2, 6):
    V = tuple(range(n))
    E = list(combinations(V[1:], 2))
    for vals in product(U, repeat=len(E)):
        A = {(0, j): 1 for j in V[1:]}
        A.update(zip(E, vals))
        A.update({(j, i): -v for (i, j), v in list(A.items())})
        good, checks = chart_case(A, V)
        charts += 1
        flat_charts += good
        chart_values += checks
    # Independently verify the real ± chart count after the pivot gauge.
    good = 0
    for vals in product((1, -1), repeat=len(E)):
        A = {(0, j): 1 for j in V[1:]}
        A.update(zip(E, vals))
        A.update({(j, i): -v for (i, j), v in list(A.items())})
        good += chart_case(A, V)[0]
    assert good == factorial(n-1)

random_values = 0
for n in range(6, 12):
    for _ in range(25):
        V = list(range(n))
        R.shuffle(V)
        cut = R.randint(1, n-1)
        trees = [random_tree(V[:cut]), random_tree(V[cut:])]
        A = {(i, j): 0 for i, j in combinations(range(n), 2)}
        A.update({(j, i): 0 for i, j in list(A)})
        for T in trees:
            fill(T, A)
        ds = [R.choice(U) for i in range(n)]
        for i, j in A:
            A[i, j] *= ds[i]*ds[j]
        order = sum(map(leaves, trees), [])
        for S in even_subsets(tuple(range(n))):
            a, v = parity_value(trees[0], set(S))
            b, w = parity_value(trees[1], set(S))
            ph = sign_in_order(S, order)*v*w if not(a or b) else 0
            for i in S:
                ph *= ds[i]
            assert pfaffian(A, S) == ph
            random_values += 1


def partitions(n):
    def go(used, blocks):
        if used == n:
            yield tuple(map(tuple, blocks))
            return
        for B in blocks:
            B.append(used)
            yield from go(used+1, blocks)
            B.pop()
        blocks.append([used])
        yield from go(used+1, blocks)
        blocks.pop()

    yield from go(0, [])


def stirling1(n, k):
    if n == 0:
        return int(k == 0)
    if k <= 0 or k > n:
        return 0
    return stirling1(n-1, k-1)+(n-1)*stirling1(n-1, k)


partition_count = 0
for n in range(1, 8):
    totals = [0]*(n+1)
    for P in partitions(n):
        if n <= 6:
            color = {v: b for b, C in enumerate(P) for v in C}
            crossing = any(
                color[a] == color[c] != color[b] == color[d]
                for a, b, c, d in combinations(range(n), 4)
            )
            A = {(i, j): int(color[i] == color[j])
                 for i, j in combinations(range(n), 2)}
            A.update({(j, i): -z for (i, j), z in list(A.items())})
            assert crossing == any(
                pfaffian(A, S) == -1 for S in even_subsets(tuple(range(n)))
            )
        w = 1
        for C in P:
            w *= factorial(len(C)-1)
        totals[len(P)] += w
        partition_count += 1
    assert totals == [stirling1(n, k) for k in range(n+1)]


def bit(a, y):
    mask, c = a
    return (int(mask & y).bit_count() + c) & 1


def phase_sum(W, y):
    return sum(w*bit(a, y)*bit(b, y) for w, a, b in W)


def expand(W):
    C = {}

    def add(s, w):
        C[s] = C.get(s, 0)+w

    for w, (a, ca), (b, cb) in W:
        add(0, w)
        add(a, -w*(-1)**ca)
        add(b, -w*(-1)**cb)
        add(a ^ b, w*(-1)**(ca+cb))
    return [(u, a) for u, a in C.items() if a]


def orbit_basis(Z, r, m):
    uu = [u for u, a in Z]
    s = len(Z)
    if s == 0:
        return Matrix(0, 0, [])
    B = hermite_normal_form((m*eye(s)).row_join(Matrix([1]*s)))
    G = [Matrix([(-1)**((u >> j) & 1) for u in uu]) for j in range(r)]
    for step in range(s*m.bit_length()+1):
        # Matrix columns, rather than rows, are the integer lattice vectors.
        old_cols = [B[:, j] for j in range(s)]
        cols = old_cols+[v.multiply_elementwise(g) for v in old_cols for g in G]
        H = hermite_normal_form(Matrix.hstack(*cols))
        if H == B:
            return H
        B = H
    raise AssertionError("too many strict index drops")


phase_cases = phase_checks = 0
for r in range(1, 7):
    for M in (2, 3, 4, 8, 19, 2**65, 2**127-1):
        for trial in range(4):
            sig = lambda: (R.randrange(2**r), R.randrange(2))
            a, b = sig(), sig()
            c = (a[0] ^ b[0], a[1] ^ b[1])
            one = (0, 1)
            W = [(2, a, b), (-1, a, one), (-1, b, one), (1, c, one)]
            if trial == 1:
                W += [(M, sig(), sig())]
            if trial >= 2:
                W += [(R.randrange(1, M), sig(), sig()) for _ in range(trial)]
            Z = expand(W)
            m = 4*M
            flat = True
            for y in range(2**r):
                z = sum(a*(-1)**((u & y).bit_count() & 1) for u, a in Z)
                assert z == 4*phase_sum(W, y)
                flat &= (z % m == 0)
                phase_checks += 1
            H = orbit_basis(Z, r, m)
            if Z:
                coef = Matrix([[a for u, a in Z]])
                assert flat == all(int(x) % m == 0 for x in coef*H)
            else:
                assert flat
            if trial < 2:
                assert flat
            phase_cases += 1

print("PASS: charts/flat/chart Pfaffians, mixed trees, partitions, phase cases/points")
print(charts, flat_charts, chart_values, random_values, partition_count,
      phase_cases, phase_checks)
