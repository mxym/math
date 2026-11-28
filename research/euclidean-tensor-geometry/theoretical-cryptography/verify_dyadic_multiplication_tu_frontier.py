#!/usr/bin/env python3
"""Exact checks for dyadic coefficient-block and signed-winding statements."""

from itertools import combinations, product


def det(A):
    n = len(A)
    if not n:
        return 1
    A = [list(row) for row in A]
    prev, sg = 1, 1
    for k in range(n-1):
        j = next((j for j in range(k, n) if A[j][k]), None)
        if j is None:
            return 0
        if j != k:
            A[j], A[k] = A[k], A[j]
            sg = -sg
        pk = A[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                num = A[i][j]*pk - A[i][k]*A[k][j]
                assert num % prev == 0
                A[i][j] = num // prev
        prev = pk
    return sg*A[-1][-1]


def matrix(f):
    n = len(f)
    return [[f[(i-j) % n]*(1 if i >= j else -1) for j in range(n)]
            for i in range(n)]


def sub(A, I, J):
    return [[A[i][j] for j in J] for i in I]


def valuation2(i):
    return (i & -i).bit_length()-1


def obstruction(f):
    supp = [i for i, v in enumerate(f) if v]
    _, u, v = max((valuation2(v-u), u, v) for u, v in combinations(supp, 2))
    g = 1 << valuation2(v-u)
    r = u % g
    assert [i for i in supp if i % g == r] == [u, v]
    return u, v, g, r


def cycle_witness(f, p=None):
    n = len(f)
    u, v, g, r = obstruction(f)
    m = n//g
    cols = tuple(range(0, n, g))
    rows = tuple(range(r, n, g))
    B = sub(matrix(f), rows, cols)
    assert abs(det(B)) == abs(f[u]**m+f[v]**m)
    a, b = u//g, v//g
    # Work in the original selected row coordinates. In cycle order,
    # the diagonal location for extra column j is alpha + j.
    J = tuple((k*(b-a)) % m for k in range(m))
    I = tuple((a+j) % m for j in J)
    ref = [[int(i == j) for i in range(m)] for j in I]
    ext = [[B[i][j] for i in range(m)] for j in J]
    contr = ext[:m-2]
    rem = [ref[0], ref[-1], ext[-2], ext[-1]]
    for x, y in combinations(rem, 2):
        D = det(contr+[x, y])
        assert D != 0 if p is None else D % p != 0


witness_cases = 0
for n in (2, 4, 8):
    for f in product((-1, 0, 1), repeat=n):
        if sum(bool(x) for x in f) < 2:
            continue
        cycle_witness(f)
        witness_cases += 1


def minors_match_binary(f, p):
    n = len(f)
    A = matrix(f)
    Z = [[int(a % p != 0) for a in row] for row in A]
    for k in range(1, n+1):
        for I, J in product(combinations(range(n), k), repeat=2):
            if bool(det(sub(A, I, J)) % p) != bool(det(sub(Z, I, J)) % 2):
                return False
    return True


field_cases = 0
for n, p in ((2, 3), (4, 3), (2, 7), (4, 7)):
    passing = uu = total_units = 0
    for f in product(range(p), repeat=n):
        s = sum(bool(x) for x in f)
        if s >= 2:
            cycle_witness(f, p)
        yes = minors_match_binary(f, p)
        passing += yes
        if det(matrix(f)) % p:
            total_units += 1
            uu += yes
        assert yes == (s <= 1)
        field_cases += 1
    assert passing == 1+n*(p-1)
    assert uu == n*(p-1)
    if n == 2 and p == 3:
        assert total_units == p*p-1
assert minors_match_binary((1, 2), 5)
assert det(matrix((1, 2))) % 5 == 0


def cycles(n, w):
    arcs = [(j, (j+h) % n, int(j+h >= n), int(h == w))
            for h in (1, w) for j in range(n)]
    adj = [[] for _ in range(n)]
    for j, (a, b, sg, lk) in enumerate(arcs):
        adj[a].append((b, j))
        adj[b].append((a, j))
    result = set()

    def dfs(root, last, V, E, parity, long):
        for nxt, edge in adj[last]:
            if edge in E or nxt < root:
                continue
            sg, lk = arcs[edge][2:]
            if nxt == root:
                if len(V) >= 2 and parity ^ sg:
                    result.add((sum(1 << x for x in V), long+lk))
            elif nxt not in V:
                dfs(root, nxt, V+[nxt], E+[edge], parity ^ sg, long+lk)

    for i in range(n):
        dfs(i, i, [i], [], 0, 0)
    return tuple(result)


minor_cases = cycle_cases = 0
for n in range(3, 9):
    for w in range(2, n):
        C = cycles(n, w)
        assert C
        disj = lambda s, t: (s[0] & t[0]) == 0
        mn = min((a[1]+b[1] for a, b in combinations(C, 2) if disj(a, b)),
                 default=n+1)
        masks = {v for v, _ in C}
        pack = {0: 0}
        for v in masks:
            for t, k in list(pack.items()):
                if not(v & t):
                    pack[v | t] = max(pack.get(v | t, 0), k+1)
        count = max(pack.values())
        assert mn >= (n+w-2)//(w-1)
        A = matrix([1]*w+[0]*(n-w))
        lo, hi = n+1, 0
        for k in range(1, n+1):
            for I, J in product(combinations(range(n), k), repeat=2):
                d = abs(det(sub(A, I, J)))
                if d > 1:
                    lo = min(lo, k)
                hi = max(hi, d)
                assert not d or (d & (d-1)) == 0
                minor_cases += 1
        assert (lo, hi) == (mn, 1 << (count-1))
        cycle_cases += len(C)


sharp_cases = 0
for s in range(2, 8):
    n = 1 << s
    for a in range(1, s):
        g, w = 1 << a, (1 << a)+1
        A = matrix([1]*w+[0]*(n-w))
        J = tuple(range(g-1, n, g))
        assert len(J) == n//g
        assert abs(det(sub(A, J, J))) == 2
        if n <= 32:
            assert abs(det(A)) == 1
        sharp_cases += 1

print("PASS: block U(2,4), odd-field support, full minors, graph cases, sharp principal")
print(witness_cases, field_cases, minor_cases, cycle_cases, sharp_cases)
