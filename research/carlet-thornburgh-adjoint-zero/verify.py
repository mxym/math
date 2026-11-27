#!/usr/bin/env python3
"""Direct derivative / plane counting and independent near-bent spectra."""
from collections import Counter
from itertools import combinations
from hashlib import sha256

N = 1024
P = 0x409


def mul(x, y):
    z = 0
    while y:
        if y & 1:
            z ^= x
        y >>= 1
        x <<= 1
        if x & N:
            x ^= P
    return z


def power(x, e):
    z = 1
    while e:
        if e & 1:
            z = mul(z, x)
        x = mul(x, x)
        e >>= 1
    return z


def tr(x):
    s = 0
    for _ in range(10):
        s ^= x
        x = mul(x, x)
    assert s in (0, 1)
    return s


def mobius(t):
    a = t[:]
    for i in range((len(t)-1).bit_length()):
        for j in range(len(t)):
            if j & (1 << i):
                a[j] ^= a[j ^ (1 << i)]
    return a


def check_apn(t):
    assert max(i.bit_count() for i, v in enumerate(mobius(t)) if v) == 2
    for d in range(1, len(t)):
        c = Counter(t[x] ^ t[x ^ d] for x in range(len(t)))
        assert len(c) == len(t)//2 and set(c.values()) == {2}


def plane_counts(t, h):
    c = [0]*len(t)
    for x, y in combinations(sorted(set(h)-{0}), 2):
        z = x ^ y
        if z > y:
            c[t[0] ^ t[x] ^ t[y] ^ t[z]] += 1
    assert c[0] == 0 and sum(c) == (len(h)-1)*(len(h)-2)//6
    return c


def fwt(t):
    w = t[:]
    for k in range((len(w)-1).bit_length()):
        h = 1 << k
        for p in range(0, len(w), 2*h):
            for a in range(p, p+h):
                b = a+h
                x, y = w[a], w[b]
                w[a], w[b] = x+y, x-y
    return w


def span_basis(h):
    basis = []
    span = [0]
    for x in h:
        if x not in span:
            basis.append(x)
            span += [s ^ x for s in span]
    assert len(span) == len(h) and set(span) == set(h)
    return basis, span


def near_bent(table, h, trace_mask):
    _, points = span_basis(h)
    return [int(max(map(abs, fwt([1-2*((b & table[x]).bit_count()%2)
                                 for x in points]))) == 32)
            for b in trace_mask]


def dot(x, y):
    return (x & y).bit_count()%2


def short(t):
    return sha256(bytes(t)).hexdigest()


def main():
    # Primitive element: exact multiplicative order 1023.
    # The 1023 distinct unit powers of 2 then comprise every nonzero residue.
    assert power(2, 1023) == 1
    powers = tuple(power(2, 1023//p) for p in (3, 11, 31))
    assert all(x != 1 for x in powers)
    print(f"n=10 field: modulus=0x{P:x} primitive-element order=1023; checks={powers}")
    a = 2
    t = [power(x, 3) ^ mul(power(a, 1022), tr(mul(power(a, 3), power(x, 9))))
         for x in range(N)]
    check_apn(t)
    print("n=10 quadratic degree=2; all 1023 derivative rows have 512 values of multiplicity 2")
    mask = [sum(tr(mul(u, 1 << i)) << i for i in range(10)) for u in range(N)]
    assert len(set(mask)) == N
    for u in (1, 2):
        h = [x for x in range(N) if not dot(mask[u], x)]
        c = plane_counts(t, h)
        odd = sum(x%2 for x in c[1:])
        g = near_bent(t, h, mask)
        anf = mobius(g)
        degree = max(i.bit_count() for i, val in enumerate(anf) if val)
        top = [i for i, val in enumerate(anf) if val and i.bit_count() == degree]
        parity = [sum(g[x] for x in range(N) if dot(mask[v], x))%2
                  for v in range(N)]
        assert sum(g)%4 == 2 and parity[1:] == [1 ^ x%2 for x in c[1:]]
        print(f"n=10 u={u}: H={len(h)} planes={sum(c)} odd_counts={odd}; "
              f"near-bent weight={sum(g)} degree={degree} first top monomial=0x{top[0]:03x}")
        if u == 1:
            assert odd == 1023 and degree == 8 and not any(parity)
            print("n=10 u=1 histogram (m, number of masks):", sorted(Counter(c[1:]).items()))
            print("n=10 u=1 near-bent truth SHA256:", short(g))
        else:
            assert odd == 511 and degree == 9 and sum(parity) == 512

    coeff = bytes.fromhex("01 02 04 08 10 40 04 06 10 18 2c 08 20 40 35 40 61 45 2a 6e 6f")
    pairs = [((1<<i) | (1<<j), c) for (i,j), c in zip(combinations(range(7),2), coeff)]
    t7 = [0]*128
    for x in range(128):
        for mask_ij, c in pairs:
            if x & mask_ij == mask_ij:
                t7[x] ^= c
    assert short(t7) == "7c7d617ac8b991b551e9a58185e81c929edaa595e60185e9bee4f9011ed9971b"
    check_apn(t7)
    zeros = []
    for u in range(1,128):
        c = plane_counts(t7, [x for x in range(128) if not dot(u,x)])
        if all(z%2 for z in c[1:]):
            zeros.append(u)
    assert zeros == [77,111]
    print(f"n=7 QAPN-7-7 row 4: all 127 derivative rows APN; nonzero adjoint zeros {zeros}")
    for u in zeros:
        c = plane_counts(t7, [x for x in range(128) if not dot(u,x)])
        print(f"n=7 u={u}: planes={sum(c)} histogram", sorted(Counter(c[1:]).items()))
    print("PASS: direct multiplicities, ANF and Walsh spectra")


if __name__ == "__main__":
    main()
