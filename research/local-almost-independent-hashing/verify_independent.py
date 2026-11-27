"""Independent exact walk operators, layout arithmetic, stripe sampling."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import isqrt
from random import Random


def ceildiv(x, y):
    return (x+y-1)//y


def clog2(x):
    return (x-1).bit_length()


def layout(n, w, k, u, code_columns):
    b = min(w, n, isqrt(w*u))
    assert 1 <= b <= w and b*b <= w*u and b >= isqrt(w)
    cut = ceildiv(n, b)
    if k*b <= w:
        key = ceildiv(k*n, w)
        assert key <= cut
        return False
    g = 1
    while 4*g*b <= w:
        g *= 4
    assert g <= w//b < 4*g and w < 4*b*g
    R = ceildiv(g, 1024)
    assert 1 <= R <= g < k and 4096*u*R > b
    base = (1 << (u+16))*k
    B = 1 << clog2(ceildiv(base, R))
    assert B*R >= base and (B//2)*R < base
    assert B*w < ((1 << (u+29))*k*b)
    inner = g.bit_length()-1 + 1280*(b-1)
    a = max(clog2(n*k)+14+ceildiv(b, 4096), B.bit_length()-1, inner)
    assert (1 << (a-14-ceildiv(b, 4096))) >= n*k
    S = 2*ceildiv((2*R+3)*a, 2)
    tau = 32*(10+ceildiv(b, 4096))
    D = ceildiv(max(4*code_columns, 32768*(n+clog2(k))), b)
    selectors = ceildiv(S+4*tau*(D-1), w)
    slots = selectors + D*B
    reads = selectors + D
    assert b*D >= 32768*(n+clog2(k)) and b*D >= 4*code_columns
    assert D <= 65537*cut  # These checks only use code_columns <= 64*n.
    assert S <= D*w
    assert 4*tau <= 1409*w
    assert 1411*D >= selectors and reads <= 1412*D
    assert (1 << (u+50))*ceildiv(k*n, w) >= slots
    if R >= 2:
        assert b >= 1022 and Q(b, 2) >= 14+Q(b, 4096)
    return True


def walk_integer(mod):
    res = list(product(range(mod), repeat=2))
    index = {v: j for j, v in enumerate(res)}
    out = [[0]*len(res) for _ in res]
    for i, (x, y) in enumerate(res):
        def put(u, v):
            out[i][index[u % mod, v % mod]] += 1
        for sign, c in product((-1, 1), range(2)):
            put(x+sign*(2*y+c), y)
            put(x, y+sign*(2*x+c))
        out[i][i] += 8
    assert all(sum(row) == 16 for row in out)
    assert all(out[i][j] == out[j][i] for i in range(len(res)) for j in range(len(res)))
    return out


def pd_assert(matrix):
    # Rational Schur complement (no numerical eigenvalue test).
    V = [row[:] for row in matrix]
    while V:
        d = V[0][0]
        assert d > 0
        V = [[u - V[i+1][0]*V[0][j+1]/d for j, u in enumerate(row[1:])]
             for i, row in enumerate(V[1:])]


def markov_joint(P, masks, gaps):
    V = [int(masks[0] >> j & 1) for j in range(len(P))]
    for M, gap in zip(masks[1:], gaps):
        for _ in range(gap):
            V = [sum(x*r for x, r in zip(V, row)) for row in P]
        V = [x if M >> j & 1 else 0 for j, x in enumerate(V)]
    return Q(sum(V), len(P)*16**sum(gaps))


def run_spectral_checks():
    rng = Random(781067)
    count = 0
    for mod in (1, 2, 4):
        P = walk_integer(mod)
        V = len(P)
        J = Q(1, V)
        centered = [[Q(P[i][j],16)-J for j in range(V)] for i in range(V)]
        rho = Q(31,32)
        for sign in (-1, 1):
            pd_assert([[rho*(i == j)+sign*centered[i][j]
                        for j in range(V)] for i in range(V)])
        if V <= 4:
            todos = [((A, B, C), (1, 2))
                     for A, B, C in product(range(1 << V), repeat=3)]
        else:
            todos = [(tuple(rng.randrange(1 << V) for _ in range(rng.randint(2, 5))),
                      ()) for _ in range(144)]
            todos = [(M, tuple(rng.randrange(1, 4) for _ in M[1:])) for M, _ in todos]
        for masks, gaps in todos:
            mu = Q(max(x.bit_count() for x in masks), V)
            bound = mu
            for g in gaps:
                bound *= mu+rho**g
            assert markov_joint(P, masks, gaps) <= bound
            count += 1
    # Degenerate transition is a marked-set trap; the strict spectral
    # requirement is real even when all one-time marginals are uniform.
    I = [[16*(i == j) for j in range(16)] for i in range(16)]
    assert markov_joint(I, (1,)*4, (1,1,1)) == Q(1,16)
    assert Q(1,16) > Q(1,16)*(Q(1,16)+Q(1,8))**3
    print(f"PASS rational spectral certificates: 3 lazy graphs and {count} fixed-set "
          "hitting cases, unequal sets/skipped times; trap rejected")


def run_accounting():
    cases = Counter()
    for n in (1, 2, 3, 4, 5, 8, 16, 31, 32, 33, 100, 257, 4099, 20001):
        G = n if n < 8 else 2**min(n, 128)
        ks = {1, min(n, 2**n), min(n*n, 2**n), G}
        ws = {1, min(2,n*n), n, n*n, max(1,n*n-1),
              min(n*n,clog2(2*n)), min(n*n,clog2(2*n)**2)}
        us = {1, 2 if n > 1 else 1, clog2(2*n)}
        for w, k, u, c in product(ws, ks, us, (4*n, 16*n, 64*n)):
            case = layout(n, w, k, u, c)
            cases["walk" if case else "exact"] += 1
    assert cases["walk"] and cases["exact"]
    print(f"PASS integer key layout: {sum(cases.values())} cases through n=20001 "
          f"({cases['walk']} walk, {cases['exact']} exact); selector bits, "
          "whole-word padding, read bound and amplification")
    # Fixed base n=2 balanced matrix, padded with full repeated column
    # blocks and zeros. Every nonzero row combo remains above 1/4.
    A0 = (1, 2, 3)
    seen = 0
    for L in range(12, 65):
        A = A0*(L//3)+(0,)*(L%3)
        for x in (1, 2, 3):
            assert 4*sum((x&v).bit_count() & 1 for v in A) > L
            seen += 1
    print(f"PASS exact repeated-matrix padding: {seen} row/length checks")


def run_stripes():
    P = walk_integer(2)
    hist = Counter()
    # The word uses three stripes of four bits. Enumerate initial point
    # and one unpowered lazy step between stripes, ignoring data values.
    for i, j, k in product(range(4), repeat=3):
        mass = P[i][j]*P[j][k]
        if mass:
            loc = i, 4+j, 8+k
            assert len(set(loc)) == 3 and all(0 <= p < 12 for p in loc)
            hist[loc] += mass
    assert sum(hist.values()) == 4*16**2
    assert len(hist) == 36
    for stripe in range(3):
        check = Counter()
        for a, z in hist.items():
            check[a[stripe]-4*stripe] += z
        assert set(check.values()) == {256}
    print(f"PASS inner striping: {len(hist)} distinct samples, one bit per stripe, "
          "uniform one-time marginals without independent transitions")


if __name__ == "__main__":
    run_spectral_checks()
    run_accounting()
    run_stripes()
