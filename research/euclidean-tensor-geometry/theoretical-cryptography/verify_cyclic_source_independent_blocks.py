#!/usr/bin/env python3
"""Exact small checks of the known-input cyclic-noise factorization rule."""

from collections import Counter
from itertools import product
from math import gcd
from random import Random

R = Random(120370)


def zeros(d):
    return (0,)*d


def add(x, y, q):
    return tuple((a+b) % q for a, b in zip(x, y))


def mul(x, a, q):
    return tuple((a*b) % q for b in x)


def effects(sources, q, d):
    A = {zeros(d): 1}
    for c, w in sources:
        B = Counter()
        for x, v in A.items():
            for a, u in enumerate(w):
                if u:
                    B[add(x, mul(c, a, q), q)] += v*u
        A = dict(B)
    return A


def project(x, I):
    return tuple(t if i in I else 0 for i, t in enumerate(x))


def independent(A, parts, q, d):
    Z = sum(A.values())
    P = [Counter() for _ in parts]
    for x, v in A.items():
        for T, I in zip(P, parts):
            T[project(x, I)] += v
    for x in product(range(q), repeat=d):
        rhs = 1
        for T, I in zip(P, parts):
            rhs *= T[project(x, I)]
        if A.get(x, 0)*Z**(len(parts)-1) != rhs:
            return False
    return True


def char_support(w, p, e):
    # Integer criterion for Phi_{p^j} divisibility.
    live = []
    for j in range(1, e+1):
        b = p**j
        accum = [0]*b
        for i, wi in enumerate(w):
            accum[i % b] += wi
        dead = all(len({accum[r+i*(b//p)] for i in range(p)}) == 1
                   for r in range(b//p))
        if not dead:
            live.append(j)
    return len(live) if live == list(range(1, len(live)+1)) else None


def predicts(sources, parts, p, e, d):
    q = p**e
    H = {zeros(d)}
    for c, w in sources:
        a = char_support(w, p, e)
        if a is None:
            return None
        H = {add(x, mul(c, p**a*t, q), q)
             for x in H for t in range(p**(e-a))}
    if any(project(x, I) not in H for x in H for I in parts):
        return False
    for c, w in sources:
        pos = [a for a, v in enumerate(w) if v]
        V = (mul(c, a-pos[0], q) for a in pos)
        V = list(V)
        if not any(all(tuple((a-b) % q for a, b in zip(x, project(x, I))) in H
                       for x in V) for I in parts):
            return False
    return True


law_cases = law_pass = subgroups = omitted = 0
for p, e in ((3, 1), (5, 1), (3, 2)):
    q = p**e
    for _ in range(240):
        d = 2
        sources = []
        for _ in range(R.randrange(1, 5)):
            c = (R.randrange(q), R.randrange(q))
            mode = R.randrange(5)
            if mode == 0:
                w = (1,)*q
                subgroups += 1
            elif mode == 1:
                a = R.randrange(q)
                w = tuple(int(j == a) for j in range(q))
            elif mode == 2:
                k = p**R.randrange(e+1)
                a = R.randrange(k)
                w = tuple(int(j % k == a) for j in range(q))
                subgroups += k < q
            elif mode == 3:
                a = R.randrange(q)
                b = (a+R.randrange(1, q)) % q
                w = tuple(2*int(j == a)+int(j == b) for j in range(q))
            else:
                w = tuple(R.randrange(1, 6) for _ in range(q))
            sources.append((c, w))
        parts = ((0,), (1,))
        s = predicts(sources, parts, p, e, d)
        if s is None:
            omitted += 1
            continue
        A = effects(sources, q, d)
        assert s == independent(A, parts, q, d)
        law_cases += 1
        law_pass += s


def shift(f, j, q):
    n = len(f)
    return tuple(f[(i-j) % n]*(1 if i >= j else -1) % q for i in range(n))


def predicted_d(G):
    n = len(G[0])
    d = n
    for f in G[1:]:
        supp = [i for i, v in enumerate(f) if v]
        if supp:
            for i in supp:
                d = gcd(d, i-supp[0])
    return d


ring_cases = ring_blocks = 0
for n, q in ((2, 3), (4, 3), (2, 9)):
    for _ in range(60):
        G = [(1,)+(0,)*(n-1)]
        for _ in range(2):
            a = R.choice([1, 2])
            t = R.randrange(a)
            G.append(tuple(R.randrange(q) if i % a == t else 0 for i in range(n)))
        d = predicted_d(G)
        src = [(shift(f, j, q), (2, 1)+(0,)*(q-2))
               for f in G for j in range(n)]
        A = effects(src, q, n)
        parts = tuple(tuple(i for i in range(n) if i % d == t) for t in range(d))
        assert independent(A, parts, q, n)
        for M in range(1, 2**(n-1)):
            I = tuple(i for i in range(n) if (M >> i) & 1)
            J = tuple(i for i in range(n) if i not in I)
            yes = all((i in I) == (k in I)
                      for i in range(n) for k in range(n) if i % d == k % d)
            assert yes == independent(A, (I, J), q, n)
            ring_cases += 1
        ring_blocks += d


counts = rows = 0
for n, q in ((4, 3), (8, 3), (2, 9)):
    for a in (1, 2, 4, 8):
        if n % a:
            continue
        got = 0
        for f in product(range(q), repeat=n):
            d = predicted_d(((1,)+(0,)*(n-1), f))
            got += d % a == 0
            rows += 1
        assert got == 1+a*(q**(n//a)-1)
        counts += 1

print("PASS: law cases/product/subgroup inputs/skipped, ring bipartitions/blocks, counts/vectors")
print(law_cases, law_pass, subgroups, omitted, ring_cases, ring_blocks, counts, rows)
