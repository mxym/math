#!/usr/bin/env python3
"""Finite checks of supplied-product forward weights and scaling counts."""

from collections import Counter
from itertools import product
from random import Random

RNG = Random(486697)


def mul(a, b, q):
    n = len(a)
    z = [0]*n
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            k = i+j
            z[k % n] += x*y if k < n else -x*y
    return tuple(t % q for t in z)


def qadd(a, b, q):
    return tuple((x+y) % q for x, y in zip(a, b))


def qsub(a, b, q):
    return tuple((x-y) % q for x, y in zip(a, b))


def scale(a, t, q):
    return tuple((x*t) % q for x in a)


def mo(a, b, q):
    return tuple(sum(t*x for t, x in zip(row, b)) % q for row in a)


def image(A, xs, q):
    n, h, r = len(xs), len(A[0]), len(A)-1
    b = []
    for j in range(n):
        z = (0,)*h
        for t in range(r+1):
            u = mo(A[t], xs[(j-t) % n], q)
            z = qadd(z, u if j >= t else scale(u, -1, q), q)
        b.append(z)
    return tuple(b)


def literal(A, table, q):
    n, m = len(table), len(table[0])
    hist = Counter()
    for raw in product(range(q), repeat=n*m):
        x = tuple(raw[j*m:(j+1)*m] for j in range(n))
        w = 1
        for j, u in enumerate(x):
            for i, xi in enumerate(u):
                w *= table[j][i][xi]
        if w:
            hist[image(A, x, q)] += w
    return hist


def transfer(A, table, out, q):
    # Check-only realization; enumerate forward input effects directly.
    n, m = len(table), len(table[0])
    r, h = len(A)-1, len(A[0])
    Z = (0,)*(h*r)

    def J(z):
        return z[h:]+(0,)*h if r else ()

    def P(z):
        return z[:h] if r else (0,)*h

    def B(u):
        return sum((mo(A[t], u, q) for t in range(1, r+1)), ())

    W = {Z}
    for i in range(m):
        z = B(tuple(int(i == j) for j in range(m)))
        for _ in range(r):
            W = {qadd(w, scale(z, k, q), q) for w in W for k in range(q)}
            z = J(z)

    H = []
    for j in range(n):
        cnt = Counter()
        for u in product(range(q), repeat=m):
            w = 1
            for i, ui in enumerate(u):
                w *= table[j][i][ui]
            cnt[(mo(A[0], u, q), B(u))] += w
        H.append({k: w for k, w in cnt.items() if w})

    total = 0
    for st in W:
        dp = {st: 1}
        for j in range(n):
            nd = Counter()
            for z, v in dp.items():
                y = qsub(out[j], P(z), q)
                for (c, cplus), w in H[j].items():
                    if c == y:
                        end = qadd(J(z), cplus, q)
                        assert end in W
                        nd[end] += v*w
            dp = nd
        total += dp.get(scale(st, -1, q), 0)
    return total, len(W)


def rawcount(q, r, l):
    if r < 0:
        return 0
    return ((q**(r+1)-1)//(q-1))*q**((r+1)*l)


counts = probes = 0
for q, n, r in ((3, 2, 0), (3, 4, 1), (5, 2, 0)):
    R = tuple(product(range(q), repeat=n))
    small = tuple(p+(0,)*(n-r-1) for p in product(range(q), repeat=r+1))
    one = (1,)+(0,)*(n-1)
    short = set(small)
    denoms = [p for p in small if any(p)]
    mons = [p for p in denoms if next(x for x in p[::-1] if x) == 1]
    inverses = {p: next(z for z in R if mul(p, z, q) == one) for p in mons}
    for l in range(0, 3):
        representable = set()
        for p in mons:
            inv = inverses[p]
            for ps in product(small, repeat=l):
                representable.add(tuple(mul(p_i, inv, q) for p_i in ps))
        exact = rawcount(q, r, l)-q*rawcount(q, r-1, l)
        assert len(representable) == exact
        for g in product(R, repeat=l):
            trial = any(all(mul(p, fi, q) in short for fi in g) for p in denoms)
            assert trial == (g in representable)
            probes += 1
        counts += 1

# Mod-p kernel need not be the reduction of the mod-p^2 kernel.
test = (0, 0, 3, 0)
for a, b in product(range(9), repeat=2):
    h = mul((a, b, 0, 0), test, 9)
    assert (h[2:] == (0, 0)) == (a % 3 == b % 3 == 0)


def example(q, n, m, h, r):
    A = tuple(tuple(tuple(RNG.randrange(q) for _ in range(m))
                    for _ in range(h)) for _ in range(r+1))
    table = tuple(tuple(tuple(RNG.randrange(4) for _ in range(q))
                        for _ in range(m)) for _ in range(n))
    return A, table


mass_cases = positive_cases = 0
for params in ((3, 2, 2, 1, 1), (3, 4, 1, 2, 2),
               (3, 4, 2, 1, 1), (3, 2, 3, 2, 0), (9, 2, 1, 1, 1)):
    q, n, m, h, r = params
    for _ in range(7):
        A, table = example(*params)
        hist = literal(A, table, q)
        out = list(hist)
        RNG.shuffle(out)
        out = out[:12]+[tuple(tuple(RNG.randrange(q) for _ in range(h))
                              for _ in range(n)) for _ in range(7)]
        for y in out:
            a, s = transfer(A, table, y, q)
            assert a == hist.get(y, 0) and s <= q**(h*r)
            mass_cases += 1
            positive_cases += a > 0

# A nonfield check with a proper additive reachable subgroup.
A = (((1,),), ((3,),))
W = (((1, 0, 2, 0, 0, 3, 0, 2, 1),),)*2
for y, w in literal(A, W, 9).items():
    assert transfer(A, W, y, 9) == (w, 3)
    mass_cases += 1

# A single fixed input, whose boundary contribution must be negated.
A = (((1,),), ((1,),))
wt = (((1, 0, 0),),)*3+(((0, 1, 0),),)
assert transfer(A, wt, ((2,), (0,), (0,), (1,)), 3)[0] == 1
assert transfer(A, wt, ((1,), (0,), (0,), (1,)), 3)[0] == 0

print("PASS: count ensembles/ratio probes, signed weighted checks/nonzero, 81 lifts")
print(counts, probes, mass_cases, positive_cases)
