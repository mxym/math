#!/usr/bin/env python3
"""Finite exact checks for ring-lwe-constant-pass-memory-lower-bound.md."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import isqrt

PHI = {
    3: (1, 1, 1),
    5: (1, 1, 1, 1, 1),
    9: (1, 0, 0, 1, 0, 0, 1),
    15: (1, -1, 0, 1, -1, 1, 0, -1, 1),
}


def reduce_z(terms, q):
    phi = PHI[q]
    a = [0] * q
    for k, c in terms:
        a[k % q] += c
    for i in range(q - 1, len(phi) - 2, -1):
        c = a[i]
        for j, f in enumerate(phi):
            a[i - len(phi) + 1 + j] -= c * f
        assert a[i] == 0
    return tuple(a[:len(phi)-1])


def mul(a, b, q):
    d = len(a)
    c = [0] * d
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[(i+j) % d] += (1 if i+j < d else -1) * x * y
    return tuple(x % q for x in c)


def adj(a, q):
    return a[:1] + tuple((-x) % q for x in reversed(a[1:]))


def add(a, b, q):
    return tuple((x+y) % q for x, y in zip(a, b))


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def exact_odd():
    identities = fibers = rounded = 0
    for q, d in ((3, 2), (3, 4), (5, 2), (9, 2), (15, 1)):
        V = list(product(range(q), repeat=d))
        n = len(V)
        modes = V[1:] if n < 30 else V[1:15] + V[::13][1:]
        for w in modes:
            images = Counter(mul(adj(a, q), w, q) for a in V)
            assert len(set(images.values())) == 1
            candidates = V[::max(1, n // 7)]
            for a, s in product(candidates, repeat=2):
                assert (dot(w, mul(a, s, q)) - dot(mul(adj(a, q), w, q), s)) % q == 0
                identities += 1
            # Arbitrary deterministic sign table tests the exact phase selector,
            # with no need for numerical evaluation of a complex phase.
            sign = {t: 1 if (dot(w, t) + dot(t, t)) % q <= (q - 1)//2 else -1 for t in V}
            chi = reduce_z(((dot(w,t), sign[t]) for t in V), q)
            for z in candidates:
                got = reduce_z(((dot(w,t) + dot(w,z), sign[add(t,z,q)]) for t in V), q)
                assert chi == got
                fibers += 1
            if q == 3:
                cos = {0: F(1), 1: F(-1,2), 2: F(-1,2)}
                counts = Counter(dot(w,t) % q for t in V)
                assert counts == {j:n//3 for j in range(3)}
                target = {j: counts[j]*cos[j] for j in counts}
                f = {j: min(range(-counts[j],counts[j]+1,2), key=lambda z:abs(z-target[j])) for j in counts}
                assert all(abs(f[j]-target[j]) <= 1 for j in counts)
                assert abs(sum(f.values())) <= 3
                # Re(DFT coefficient) bound from exact 3rd-root cosines.
                assert abs(sum(F(f[j],n)*cos[j] for j in counts)-F(1,2)) <= F(3,n)
                rounded += 1
        # Test the unnormalised Parseval/correlation form of (6) for a
        # sample of a (no restriction on the positive density).
        V = V if n <= 25 else None
        if V is not None:
            for a in V:
                w = modes[0]
                f = {t: 1 if (dot(w,t)+dot(t,t)) % q < (q+1)//2 else -1 for t in V}
                h = {s: 1 + (dot(s,s) % 5) for s in V}
                direct = n*sum(sum(h[s]*f[add(mul(a,s,q),t,q)] for s in V)**2 for t in V)
                terms = []
                for v in V:
                    av = mul(adj(a,q),v,q)
                    f_corr, h_corr = Counter(), Counter()
                    for t1,t2 in product(V,repeat=2):
                        f_corr[(dot(v,t1)-dot(v,t2)) % q] += f[t1]*f[t2]
                        h_corr[(dot(av,t1)-dot(av,t2)) % q] += h[t1]*h[t2]
                    terms.extend((r+s, k*l) for r,k in f_corr.items() for s,l in h_corr.items())
                expected = reduce_z(terms, q)
                assert expected == (direct,) + (0,)*(len(PHI[q])-2)
                identities += 1
    return identities, fibers, rounded


def binary():
    repetitions = parity_masses = 0
    for d in (2,4,8,16,32):
        for p in (1,2,4,8,16):
            if not p <= d:
                continue
            polynomial = sum(1 << (j*p) for j in range(d//p))
            # Shift once per degree: ideal basis (1+X)^(d-p)..(1+X)^(d-1).
            v = polynomial
            span = {0}
            for k in range(p):
                span |= {w ^ v for w in span}
                v ^= (v << 1) & ((1 << d) - 1)
            repeated = {sum(w << (j*p) for j in range(d//p)) for w in range(1<<p)}
            assert span == repeated
            assert all(x.bit_count() == (x & ((1 << p)-1)).bit_count()*(d//p) for x in span)
            repetitions += len(span)
            if d <= 4:
                b = F(1,11)
                integers = range(-2,3)
                e = sum(b**(j*j) for j in integers if j % 2 == 0)
                o = sum(b**(j*j) for j in integers if j % 2)
                total = 0
                for vec in product(integers,repeat=d):
                    parity = sum((x%2)<<i for i,x in enumerate(vec))
                    if parity in span and parity:
                        total += b**sum(x*x for x in vec)
                assert total == e**d*((1+(o/e)**(d//p))**p-1)
                parity_masses += 1
    exponents = 0
    for d in (2**k for k in range(8,32)):
        for B in (d.bit_length()+4, d.bit_length()**2, d//2, d, 10*d):
            D = min(d,isqrt(d*B))
            K = D//8
            p = 1 << (K-1).bit_length()
            assert K <= p <= D//4 and d % p == 0
            assert (d//p)*(B-2) >= 2*D
            exponents += 1
    return repetitions, parity_masses, exponents


def public_lift():
    rows = 0
    for N,M in ((3,8),(5,16),(9,32),(25,256)):
        fibers = tuple((M+i)//N for i in range(N))
        assert sum(fibers)==M
        f = [F(1+(i*i % 19),1) for i in range(M)]
        f = [x*M/sum(f) for x in f]
        h = []
        i = 0
        for n in fibers:
            h.append(N*sum(f[i:i+n])/M)
            i += n
        assert sum(h)==N
        assert sum(x*x for x in h)/N <= max(F(n*N,M) for n in fibers)*sum(x*x for x in f)/M
        rows += 1
    return rows


if __name__ == "__main__":
    print("PASS odd adjoints, exact phases, rounded profiles:", exact_odd())
    print("PASS binary ideals, exact parity masses, exponent arithmetic:", binary())
    print("PASS non-power-of-two secret lifts:", public_lift())
