#!/usr/bin/env python3
"""Exact sum-free, adjoint and translation-code certificates."""
from collections import Counter
from itertools import combinations
from hashlib import sha256

N = 64
PAIRS = tuple(combinations(range(6), 2))
ROW = (1,2,4,8,16,4,6,16,24,8,5,37,32,5,3)


def mul(x, y):
    z = 0
    while y:
        if y & 1:
            z ^= x
        y >>= 1
        x <<= 1
        if x & 64:
            x ^= 0x43
    return z


def power(x,e):
    y = 1
    while e:
        if e & 1:
            y = mul(y,x)
        x = mul(x,x)
        e >>= 1
    return y


def trace(x):
    y = 0
    for _ in range(6):
        y ^= x
        x = mul(x, x)
    assert y in (0,1)
    return y


def dot(x, y):
    return (x & y).bit_count() & 1


def polar(f, x, y):
    return f[x] ^ f[y] ^ f[x^y] ^ f[0]


def xor(values):
    r = 0
    for x in values:
        r ^= x
    return r


def max_derivative(f):
    return max(max(Counter(f[y] ^ f[x^y] for y in range(N)).values()) for x in range(1,N))


def planes():
    return [(u,v) for u,v in combinations(range(1,N),2) if u^v > v]


def adjoint(f, pairing_masks, two_spaces):
    out = [0]
    for u in range(1,N):
        mu = pairing_masks[u]
        m = [0]*N
        for x,y in two_spaces:
            if not dot(mu,x) and not dot(mu,y):
                m[polar(f,x,y)] += 1
        assert m[0] == 0 and sum(m) == 155
        fs = {v for v in range(1,N) if not m[v]%2}
        [c] = [c for c in range(N) if fs == {v for v in range(1,N) if dot(pairing_masks[v],c)}]
        out.append(c)
    return out


def orthoderivative(f, masks):
    p = [0]
    for x in range(1,N):
        d = [polar(f,x,1<<i) for i in range(6)]
        [v] = [v for v in range(1,N) if all(not dot(masks[v], w) for w in d)]
        p.append(v)
    return p


def flats(masks, two_spaces):
    allflats = []
    for u,v in two_spaces:
        fibers = {}
        for x in range(N):
            fibers.setdefault((dot(masks[u],x),dot(masks[v],x)),[]).append(x)
        assert len(fibers) == 4 and all(len(f)==16 for f in fibers.values())
        allflats.extend(tuple(entries) for entries in fibers.values())
    assert len(allflats) == len(set(allflats)) == 2604
    return allflats


def graph_rank(f):
    pivot = {}
    for a in range(N):
        for b in range(N):
            row = sum(1 << (((x^a)<<6) | (y^b)) for x,y in enumerate(f))
            while row:
                k = row.bit_length()
                if k not in pivot:
                    pivot[k] = row
                    break
                row ^= pivot[k]
    return len(pivot)


def check(label, f, m, two_spaces, gold_rank):
    assert all(polar(f,x,y) == xor(polar(f,1<<i,1<<j) for i in range(6) for j in range(6)
                                   if x>>i&1 and y>>j&1) for x in range(N) for y in range(N))
    assert max_derivative(f) == 2
    eps = adjoint(f,m,two_spaces)
    assert max_derivative(eps) == 2
    assert graph_rank(f) == 1146 != gold_rank
    p = orthoderivative(f,m)
    af = flats(m,two_spaces)
    sums = [xor(p[x] for x in h) for h in af]
    assert all(sums)
    q = p[:]
    q[af[0][0]] ^= sums[0]
    assert xor(q[x] for x in af[0]) == 0
    print(f"{label}: APN and adjoint APN; graph-code rank 1146; all {len(af)} affine 4-flat sums nonzero")
    print(f"{label}: 4-flat sums have {len(set(sums))} distinct nonzero values;"
          " negative control changes the selected flat's sum to zero")
    return eps


def main():
    assert power(2,63)==1 and power(2,21)!=1 and power(2,9)!=1
    f = [power(x,3)^mul(power(2,62),trace(mul(8,power(x,9)))) for x in range(N)]
    g = [power(x,3) for x in range(N)]
    r = graph_rank(g)
    assert r == 1102
    print("field 0x43: root has order 63; Gold translation-code rank 1102")
    masks = [sum(trace(mul(u,1<<i))<<i for i in range(6)) for u in range(N)]
    twos = planes()
    assert len(twos)==651
    eps = check("switched cube",f,masks,twos,r)
    expected = [power(x,3)^mul(30,power(x,9))^mul(44,power(x,18)) for x in range(N)]
    assert eps == expected
    assert max_derivative([x^y for x,y in zip(eps,g)]) > 2
    print("switched cube: exact adjoint polynomial x^3 + 0x1e*x^9 + 0x2c*x^18; dropped x^3 fails APN")
    f2 = [xor(c for c,(i,j) in zip(ROW,PAIRS) if x>>i&1 and x>>j&1) for x in range(N)]
    assert sha256(bytes(f2)).hexdigest() == "5ab7a0bd635cdb2ee8c2520d9db65a7a4c7e9c28bdd9898ba042451476b7a1db"
    check("QAPN-6-6 row 2",f2,list(range(N)),twos,r)
    print("PASS: plane multiplicities, differences, translation code and affine 4-flats")


if __name__=="__main__":
    main()
