#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt

def primes_upto(n):
    a = bytearray(b"\x01") * (n + 1)
    a[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            a[p*p:n+1:p] = b"\x00" * (((n - p*p)//p)+1)
    return [i for i in range(3, n + 1) if a[i]]

def v2(n):
    r = 0
    while n % 2 == 0:
        n //= 2
        r += 1
    return r

def order_mod(a, m, exponent):
    r, x, fac, d = exponent, exponent, [], 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fac.append(x)
    for d in fac:
        while r % d == 0 and pow(a, r//d, m) == 1:
            r //= d
    return r

def legendre(a, p):
    z = a % p
    if z == 0:
        return 0
    return -1 if pow(z, (p-1)//2, p) == p-1 else 1

def least_pair_witness(p, q):
    sp, sq = v2(p-1), v2(q-1)
    if sp != sq:
        high = p if sp > sq else q
        for a in range(2, high):
            if legendre(a, high) == -1:
                return a, high
        raise AssertionError
    Q = p*q
    for a in range(2, Q):
        if legendre(a, p) * legendre(a, q) == -1:
            return a, Q
    raise AssertionError

def h_bottleneck(ps):
    layers = {}
    for p in ps:
        layers.setdefault(v2(p-1), []).append(p)
    h = max(ps)
    for xs in layers.values():
        xs.sort()
        if len(xs) >= 2:
            h = max(h, xs[-1]*xs[-2])
    return h

def refine_one(D, E, a):
    # Saturate every prime divisor shared with a to its complete
    # prime-power component.
    L = D.bit_length()
    U = gcd(D, pow(a, L, D))
    initial = [D] if U in (1, D) else [U, D//U]
    out = []
    for X in initial:
        if gcd(a, X) != 1:
            out.append(X)
            continue
        parts = [X]
        S = v2(E)
        for j in range(S + 1):
            cut = gcd(pow(a, E//(2**j), X)-1, X)
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
    for a in range(2, B + 1):
        nxt = []
        for D in blocks:
            nxt.extend(refine_one(D, E, a))
        blocks = sorted(nxt)
    return blocks

P = primes_upto(70)
mods = []
for k in range(2, 6):
    for ps in combinations(P, k):
        N = 1
        for p in ps:
            N *= p
        if N <= 2_000_000:
            mods.append(ps)

pair_checks = 0
all_pair_refinements = 0
unique_layer_cases = 0
for ps in mods:
    E = 1
    for p in ps:
        E = lcm(E, p-1)
    H = h_bottleneck(ps)
    assert H <= ps[-1]*ps[-2]
    assert H <= (E+1)**2
    if len({v2(p-1) for p in ps}) == len(ps):
        assert H == ps[-1] <= E+1
        unique_layer_cases += 1

    B = 2
    for p, q in combinations(ps, 2):
        a, Q = least_pair_witness(p, q)
        assert a <= Q <= H
        sp, sq = v2(p-1), v2(q-1)
        if sp != sq:
            high, low = (p, q) if sp > sq else (q, p)
            assert legendre(a, high) == -1
            if a % low != 0:
                assert v2(order_mod(a, high, high-1)) > \
                       v2(order_mod(a, low, low-1))
        else:
            assert gcd(a, p*q) == 1
            assert legendre(a, p)*legendre(a, q) == -1
            assert v2(order_mod(a, p, p-1)) != \
                   v2(order_mod(a, q, q-1))
        B = max(B, a)
        pair_checks += 1

    N = 1
    for p in ps:
        N *= p
    assert full_refine(N, E, B) == list(ps)
    all_pair_refinements += 1

power_refinements = 0
power_block_checks = 0
smallP = primes_upto(20)
for k in range(2, 5):
    for ps in combinations(smallP, k):
        for exps in product(range(1, 4), repeat=k):
            N, E = 1, 1
            targets = []
            for p, e in zip(ps, exps):
                pe = p**e
                N *= pe
                targets.append(pe)
                E = lcm(E, p**(e-1)*(p-1))
            if N > 3_000_000:
                continue
            B = max(least_pair_witness(p, q)[0]
                    for p, q in combinations(ps, 2))
            got = full_refine(N, E, B)
            assert got == sorted(targets)
            for a in range(2, min(B, 30)+1):
                parts = refine_one(N, E, a)
                assert all(gcd(x, N//x) == 1 for x in parts)
                power_block_checks += len(parts)
            power_refinements += 1

print(f"squarefree supports: {len(mods)}")
print(f"pair forcing checks: {pair_checks}")
print(f"all-pair refinements: {all_pair_refinements}")
print(f"unique-layer supports: {unique_layer_cases}")
print(f"prime-power refinements: {power_refinements}")
print(f"complete-block checks: {power_block_checks}")
print("PASS")
