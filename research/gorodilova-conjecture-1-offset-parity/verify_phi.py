#!/usr/bin/env python3
"""Recompute phi from derivative images and the tensor splitting from planes."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from hashlib import sha256
from itertools import combinations
from math import gcd
from operator import xor
from pathlib import Path

MOD = {2:7, 3:11, 4:19, 5:37, 6:67, 7:131, 8:285, 9:529, 10:1033}
CATALOG7_SHA256 = "d829626bacfe76b8de55d41cec43edd1708e9984ece3f750692fd69623e0e0a0"


def gold(n, s):
    modulus = MOD[n]
    order = (1 << n)-1
    exps, log = [], [None]*(order+1)
    a = 1
    for k in range(order):
        assert a and log[a] is None
        exps.append(a)
        log[a] = k
        a <<= 1
        if a > order:
            a ^= modulus
    assert a == 1 and all(v is not None for v in log[1:])

    def pow_(a, k):
        return exps[(log[a]*k) % order] if a else 0

    def tr(a):
        return reduce(xor, (pow_(a, 1 << i) for i in range(n)))

    if s:
        return [pow_(a, (1 << s)+1) for a in range(order+1)]
    return [pow_(a, 3)^tr(pow_(a, 9)) for a in range(order+1)]


def top_degree(f, n):
    g = list(f)
    for j in range(n):
        for x in range(1 << n):
            if x & (1 << j):
                g[x] ^= g[x ^ (1 << j)]
    return max(i.bit_count() for i,v in enumerate(g) if v)


def check(f, n):
    N = 1 << n
    bs = tuple(1 << i for i in range(n))
    pairs = tuple(combinations(range(n), 2))
    pp = tuple((bs[i] | bs[j]) for i,j in pairs)

    def beta(a, b):
        return f[a]^f[b]^f[a^b]^f[0]

    # Derivative images and phi use the original definition, not the trace.
    phi, pi = [1], [0]
    for a in range(1, N):
        D = {f[a^x]^f[x] for x in range(N)}
        assert len(D) == N//2
        phi.append(int(0 not in D))
        basis_images = [beta(a, x) for x in bs]
        normals = [b for b in range(1, N)
                   if not any((b & v).bit_count() & 1 for v in basis_images)]
        assert len(normals) == 1
        b, = normals
        assert b != 0 and phi[-1] == ((b & (f[a]^f[0])).bit_count() & 1)
        pi.append(b)
    assert sum(phi) % 2 == (n+1) % 2
    assert (top_degree(phi, n) == n) == (n % 2 == 0)
    # Convention negative control: if phi(0) were zero, the answer would flip.
    assert (sum(phi)-phi[0]) % 2 == n % 2
    if n == 2:
        return sum(phi)
    assert reduce(xor, pi) == 0
    assert all(reduce(xor, (pi[x] for x in range(N) if x & b)) == 0 for b in bs)

    # Direct plane enumeration: each sorted nonzero triple exactly once.
    groups, wedge = [0]*N, [0]*N
    mask = [sum(((x & ij) == ij) << k for k,ij in enumerate(pp)) for x in range(N)]
    for a in range(1, N):
        for b in range(a+1, N):
            c = a^b
            if b < c:
                w = beta(a, b)
                assert w != 0
                groups[w] += 1
                wedge[w] ^= mask[a]^mask[b]^mask[c]
    assert all(m & 1 for m in groups[1:])
    if n % 2:
        assert len(set(pi)) == N
        assert set(groups[1:]) == {(N//2-1)//3}
    v_coeffs = [reduce(xor, (pi[x] for x in range(N) if x & ij == ij)) for ij in pp]
    beta_coeffs = [beta(bs[i], bs[j]) for i,j in pairs]
    for v in range(N):
        moment = sum(((v&h).bit_count() & 1) << j for j,h in enumerate(v_coeffs))
        assert wedge[v] == moment
        assert reduce(xor, (b for j,b in enumerate(beta_coeffs) if moment >> j & 1), 0) == v
    assert sum((a&b).bit_count() for a,b in zip(beta_coeffs,v_coeffs)) % 2 == n % 2
    return sum(phi)


def main():
    p = ArgumentParser()
    p.add_argument("--catalog7", type=Path)
    args = p.parse_args()
    for n in range(2, 11):
        rows = [gold(n, s) for s in range(1, n) if gcd(s, n) == 1]
        if n >= 3:
            rows.append(gold(n, 0))
            # Deterministic nontrivial affine perturbation incl. constant.
            mask = (1 << n)-1
            rows.append([v ^ ((a << 1) & mask) ^ (a >> (n-1)) ^ 3
                         for a,v in enumerate(rows[-1])])
        counts = Counter(check(row, n) for row in rows)
        print(f"n={n}: {len(rows)} QAPN maps APN/phi checks PASS; "
              f"phi weights: {sorted(counts.items())}")
    print("one-bit origin negative control: rejected in every map")
    if args.catalog7:
        data = args.catalog7.read_bytes()
        assert len(data) == 182023 and sha256(data).hexdigest() == CATALOG7_SHA256
        lines = data.decode().splitlines()
        assert all(line.endswith(",") for line in lines)
        rows = [[int(x,16) for x in line[:-1].split(",")] for line in lines]
        assert len(rows) == 488 and all(len(f) == 128 for f in rows)
        counts = Counter(check(f,7) for f in rows)
        print(f"Zenodo QAPN-7-7: {len(rows)} maps PASS; phi weights: {sorted(counts.items())}")


if __name__ == "__main__":
    main()
