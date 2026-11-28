#!/usr/bin/env python3
"""Exact rational local-flatness identities and finite repair checks."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from random import Random

R = Random(713040)
Z = 0, 0
ONE = 1, 0


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def neg(x):
    return -x[0], -x[1]


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]


def norm(x):
    return x[0]**2+x[1]**2


def dist(x, y):
    return norm(sub(x, y))


def unit(t, quadrant=0):
    u = ((1-t*t)/(1+t*t), 2*t/(1+t*t))
    rot = (ONE, (0, 1), (-1, 0), (0, -1))[quadrant]
    return mul(u, rot)


def setedge(A, i, j, z):
    A[i, j], A[j, i] = z, neg(z)


def pf(A, S):
    @lru_cache(None)
    def go(X):
        if not X:
            return ONE
        out = Z
        for j in range(1, len(X)):
            u = mul(A[X[0], X[j]], go(X[1:j]+X[j+1:]))
            out = add(out, u if j & 1 else neg(u))
        return out
    return go(tuple(S))


def modsize(A, S):
    return min(max(dist(A[i, x], A[i, y])
                   for i in S if i not in M for x, y in combinations(M, 2))
               for k in range(2, len(S)) for M in combinations(S, k))


def minimum_bad(A, k):
    return max((abs(norm(pf(A, S))-1) for S in combinations(range(k), 4)),
               default=0)


def repair(A, k, eps):
    L = {A[i, j] for i in range(1, k) for j in range(1, k) if i != j}
    code = {}
    done = set()
    diam = 0
    for z in sorted(L):
        if z in done:
            continue
        C = {z}
        pending = [z]
        while pending:
            w = pending.pop()
            for u in L-C:
                if dist(u, w) <= 27**2 * eps:
                    pending.append(u)
                    C.add(u)
        minus = {neg(u) for u in C}
        if C & minus:
            B = {}
            for i, j in combinations(range(k), 2):
                setedge(B, i, j, ONE)
            return B, False
        assert not done & (C | minus)
        done.update(C | minus)
        diam = max(diam, max(dist(x, y) for x in C for y in C))
        code.update({u: z for u in C})
        code.update({u: neg(z) for u in minus})
    B = dict(A)
    for i, j in combinations(range(1, k), 2):
        setedge(B, i, j, code[A[i, j]])
    assert max(dist(A[i, j], B[i, j]) for i, j in A) <= diam
    return B, True


def gen_tree(A, V):
    if len(V) <= 1:
        return
    i = R.randint(1, len(V)-1)
    a, b = V[:i], V[i:]
    typ = Q(R.randint(-3, 3), R.randint(2, 13))
    z = unit(typ, R.randrange(4))
    for x in a:
        for y in b:
            setedge(A, x, y, z)
    gen_tree(A, a)
    gen_tree(A, b)


trials = shadows = quadruples = pv = close = cluster = 0
for k in range(3, 9):
    for mode in range(4):
        for i in range(6):
            A = {(0, j): ONE for j in range(1, k)}
            A.update({(j, 0): neg(ONE) for j in range(1, k)})
            V = list(range(1, k))
            R.shuffle(V)
            gen_tree(A, V)
            for u, v in combinations(range(1, k), 2):
                if mode == 1:
                    z = mul(A[u, v], unit(Q(R.randint(-4, 4), 2**19)))
                elif mode == 2:
                    z = mul(A[u, v], unit(Q(R.randint(-4, 4), 2**10)))
                elif mode == 3:
                    z = unit(Q(R.randint(-7, 7), R.randint(3, 25)), R.randrange(4))
                else:
                    z = A[u, v]
                assert norm(z) == 1
                setedge(A, u, v, z)
            eps = minimum_bad(A, k)
            for S in combinations(range(1, k), 3):
                assert modsize(A, S) <= eps
                shadows += 1
            for S in combinations(range(1, k), 4):
                assert modsize(A, S) <= 27**2*eps
                quadruples += 1
            B, grouped = repair(A, k, eps)
            cluster += grouped
            eta2 = max(dist(A[u, v], B[u, v]) for u, v in A)
            assert eta2 <= min(4, 27**2*((k-1)*(k-2))**2*eps)
            for s in range(0, k+1, 2):
                for S in combinations(range(k), s):
                    p, q = pf(A, S), pf(B, S)
                    assert norm(q) == 1
                    pv += 1
                    if 4*k**4*eta2 <= 1:
                        assert dist(p, q) <= 4*k**4*eta2
                        close += 1
            trials += 1


lower = 0
for j in range(1, 100):
    U = unit(Q(1, j))
    A = {}
    for a in range(1, 5):
        setedge(A, 0, a, ONE)
    for (i, j), z in zip(combinations(range(1, 5), 2),
                         (ONE, ONE, U, neg(U), neg(ONE), U)):
        setedge(A, i, j, z)
    for S in combinations(range(1, 5), 3):
        assert modsize(A, S) == 0
        assert norm(pf(A, (0,)+S)) == 1
    e4 = minimum_bad(A, 5)
    assert e4 == 4*U[1]**2 and e4 > 0
    sep2 = dist(U, ONE)
    assert modsize(A, tuple(range(1, 5))) == sep2
    assert 4*sep2 >= e4
    lower += 1

print("PASS: generated charts, triangles, quartets, repaired values, tight radius")
print(trials, shadows, quadruples, pv, close, cluster, lower)
