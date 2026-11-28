#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt

Z = 7

def primes_upto(n, odd_only=False):
    a = bytearray(b"\x01") * (n + 1)
    a[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            a[p*p:n+1:p] = b"\x00" * (((n-p*p)//p)+1)
    return [i for i in range(3 if odd_only else 2, n+1) if a[i]]

RSET = primes_upto(Z)

def vr(n, r):
    t = 0
    while n % r == 0:
        n //= r
        t += 1
    return t

def order_mod(a, m, exponent):
    x, fac, d = exponent, [], 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fac.append(x)
    out = exponent
    for d in fac:
        while out % d == 0 and pow(a, out//d, m) == 1:
            out //= d
    return out

def legendre(a, p):
    if a % p == 0:
        return 0
    return -1 if pow(a, (p-1)//2, p) == p-1 else 1

def signature(p):
    return tuple(vr(p-1, r) for r in RSET)

def bottleneck(ps):
    classes = {}
    for p in ps:
        classes.setdefault(signature(p), []).append(p)
    h = max(ps)
    for xs in classes.values():
        xs.sort()
        if len(xs) >= 2:
            h = max(h, xs[-1]*xs[-2])
    return h

def quadratic_pair_witness(p, q):
    Q = p*q
    for a in range(2, Q):
        if legendre(a, p)*legendre(a, q) == -1:
            return a, Q, 2
    raise AssertionError

def signature_pair_witness(p, q):
    sp, sq = signature(p), signature(q)
    if sp == sq:
        return quadratic_pair_witness(p, q)
    for r, x, y in zip(RSET, sp, sq):
        if x == y:
            continue
        high, low = (p, q) if x > y else (q, p)
        d = abs(x-y)
        for a in range(2, high):
            if pow(a, (high-1)//(r**d), high) != 1:
                return a, high, r
        raise AssertionError
    raise AssertionError

def refine_one(D, E, a):
    L = D.bit_length()
    U = gcd(D, pow(a, L, D))
    initial = [D] if U in (1, D) else [U, D//U]
    out = []
    for X in initial:
        if gcd(a, X) != 1:
            out.append(X)
            continue
        parts = [X]
        for r in RSET:
            if E % r:
                continue
            S, z = 0, E
            while z % r == 0:
                z //= r
                S += 1
            for j in range(S + 1):
                raw = gcd(pow(a, E//(r**j), X)-1, X)
                cut = gcd(X, pow(raw, X.bit_length(), X))
                nxt = []
                for Y in parts:
                    g = gcd(Y, cut)
                    if 1 < g < Y:
                        nxt.extend([g, Y//g])
                    else:
                        nxt.append(Y)
                parts = nxt
        out.extend(parts)
    return out

def full_refine(N, E, B):
    blocks = [N]
    for a in range(2, B+1):
        nxt = []
        for D in blocks:
            nxt.extend(refine_one(D, E, a))
        blocks = sorted(nxt)
    return blocks

P = [p for p in primes_upto(80, odd_only=True) if p > Z]
mods = []
for k in range(2, 6):
    for ps in combinations(P, k):
        N = 1
        for p in ps:
            N *= p
        if N <= 2_000_000:
            mods.append(ps)

pair_checks = 0
all_refinements = 0
signature_unique = 0
strict_improvements = 0
for ps in mods:
    E = 1
    for p in ps:
        E = lcm(E, p-1)
    H = bottleneck(ps)
    H2classes = {}
    for p in ps:
        H2classes.setdefault(vr(p-1, 2), []).append(p)
    H2 = max(ps)
    for xs in H2classes.values():
        xs.sort()
        if len(xs) >= 2:
            H2 = max(H2, xs[-1]*xs[-2])
    assert H <= H2 <= ps[-1]*ps[-2]
    assert H <= (E+1)**2
    if H < H2:
        strict_improvements += 1
    if len({signature(p) for p in ps}) == len(ps):
        assert H == ps[-1] <= E+1
        signature_unique += 1

    B = 2
    for p, q in combinations(ps, 2):
        a, Q, r = signature_pair_witness(p, q)
        assert a < Q <= H
        sp, sq = signature(p), signature(q)
        if sp == sq:
            assert gcd(a, p*q) == 1
            assert legendre(a, p)*legendre(a, q) == -1
            assert vr(order_mod(a, p, p-1), 2) != \
                   vr(order_mod(a, q, q-1), 2)
        else:
            x, y = vr(p-1, r), vr(q-1, r)
            high, low = (p, q) if x > y else (q, p)
            assert pow(a, (high-1)//(r**abs(x-y)), high) != 1
            if a % low:
                assert vr(order_mod(a, high, high-1), r) > \
                       vr(order_mod(a, low, low-1), r)
        B = max(B, a)
        pair_checks += 1
    N = 1
    for p in ps:
        N *= p
    assert full_refine(N, E, B) == list(ps)
    all_refinements += 1

power_refinements = 0
block_checks = 0
smallP = [p for p in primes_upto(35, odd_only=True) if p > Z]
for k in range(2, 5):
    for ps in combinations(smallP, k):
        for exps in product(range(1, 4), repeat=k):
            N, E, target = 1, 1, []
            for p, e in zip(ps, exps):
                pe = p**e
                N *= pe
                target.append(pe)
                E = lcm(E, p**(e-1)*(p-1))
            if N > 3_000_000:
                continue
            B = max(signature_pair_witness(p, q)[0]
                    for p, q in combinations(ps, 2))
            assert full_refine(N, E, B) == sorted(target)
            for a in range(2, min(B, 25)+1):
                parts = refine_one(N, E, a)
                assert all(gcd(x, N//x) == 1 for x in parts)
                block_checks += len(parts)
            power_refinements += 1

print(f"small primes in signature: {RSET}")
print(f"squarefree supports: {len(mods)}")
print(f"pair forcing checks: {pair_checks}")
print(f"all-pair refinements: {all_refinements}")
print(f"signature-unique supports: {signature_unique}")
print(f"strict improvements over r=2: {strict_improvements}")
print(f"prime-power refinements: {power_refinements}")
print(f"complete-block checks: {block_checks}")
print("PASS")
