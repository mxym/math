#!/usr/bin/env python3
"""Construct the two squares, verify Latin/orthogonality and common cell orbits."""
from collections import deque
from itertools import product

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")


def check_pair(L, n):
    want = set(range(n))
    for table in L:
        assert all(set(row) == want for row in table)
        assert all(set(column) == want for column in zip(*table))
    return len({(a, b) for ra, rb in zip(*L) for a, b in zip(ra, rb)}) == n * n


def permutation(M, n):
    return set(M) == set(range(n))


def check_autotopy(L, maps):
    R, C, *S = maps
    n = len(R)
    assert all(permutation(M, n) for M in maps)
    return all(table[R[i]][C[j]] == sym[table[i][j]]
               for table, sym in zip(L, S)
               for i in range(n) for j in range(n))


def orbit_size(n, cell_maps):
    q = deque([(0, 0)])
    seen = set(q)
    while q:
        r, c = q.popleft()
        for R, C in cell_maps:
            u = R[r], C[c]
            if u not in seen:
                seen.add(u)
                q.append(u)
    return len(seen)


def verify(p):
    X = list(product(range(p), repeat=2))
    n = len(X)
    slopes = (1, 2)

    def code(x, y):
        return (x % p) * p + (y % p)

    def perm(f):
        return [code(*f(x, y)) for x, y in X]

    L = [
        [[code(x + t*u, y + t*v + t*x*x*u - 2*x*u*u)
          for u, v in X] for x, y in X]
        for t in slopes
    ]
    assert check_pair(L, n)

    def row_shift(a):
        return [
            perm(lambda x,y: (x+a,y+a*x*x)),
            perm(lambda u,v: (u,v+3*a*u*u-a*a*u)),
            *[perm(lambda z,w: (z+a,w+a*z*z)) for _ in slopes],
        ]

    def col_shift(b):
        maps = [
            perm(lambda x,y: (x,y-3*b*x*x+2*b*b*x)),
            perm(lambda u,v: (u+b,v-2*b*u*u)),
        ]
        for t in slopes:
            tinv = pow(t, -1, p)
            maps.append(perm(lambda z,w: (z+t*b,w-2*b*tinv*z*z)))
        return maps

    def fiber(r, s):
        return [
            perm(lambda x,y: (x,y+r)), perm(lambda u,v: (u,v+s)),
            *[perm(lambda z,w: (z,w+r+t*s)) for t in slopes],
        ]

    for a in range(p):
        assert check_autotopy(L, row_shift(a))
        assert check_autotopy(L, col_shift(a))
        assert check_autotopy(L, fiber(a, 0))
        assert check_autotopy(L, fiber(0, a))
    G = [row_shift(1), col_shift(1), fiber(1,0), fiber(0,1)]
    assert orbit_size(n, [g[:2] for g in G]) == n*n

    M = [[[ (a+t*b)%3 for b in range(3)] for a in range(3)] for t in slopes]
    assert check_pair(M, 3)
    DG = [
        [[(a+1)%3 for a in range(3)], list(range(3)),
         [(a+1)%3 for a in range(3)], [(a+1)%3 for a in range(3)]],
        [list(range(3)), [(b+1)%3 for b in range(3)],
         [(b+1)%3 for b in range(3)], [(b+2)%3 for b in range(3)]],
    ]
    assert all(check_autotopy(M, g) for g in DG)
    N = [
        [[3*table[i][j]+base[a][b]
          for j, b in product(range(n), range(3))]
         for i, a in product(range(n), range(3))]
        for table, base in zip(L, M)
    ]
    assert check_pair(N, 3*n)

    def direct(a, b):
        return [3*i+j for i in a for j in b]

    ext = [[direct(a, range(3)) for a in g] for g in G]
    ext += [[direct(range(n), b) for b in h] for h in DG]
    assert all(check_autotopy(N, g) for g in ext)
    assert orbit_size(3*n, [g[:2] for g in ext]) == 9*n*n

    assert not check_pair([L[0], L[0]], n)
    wrong = row_shift(1)
    wrong[2] = perm(lambda z,w: (z+1,w+2*z*z))
    assert not check_autotopy(L, wrong)
    print(f"p={p}: base order={n}, product order={3*n}, "
          f"joint product cell orbit={9*n*n}; negative controls PASS")


if __name__ == "__main__":
    for p in (5,7,11):
        verify(p)
    print("PASS construction")
