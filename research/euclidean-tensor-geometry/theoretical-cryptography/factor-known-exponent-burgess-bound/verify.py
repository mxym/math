#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt

def primes_upto(n):
    a = bytearray(b"\x01") * (n + 1)
    a[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            a[p*p:n+1:p] = b"\x00" * (((n - p*p) // p) + 1)
    return [i for i in range(3, n + 1) if a[i]]

def v2(n):
    s = 0
    while n % 2 == 0:
        s += 1
        n //= 2
    return s

def order_mod(a, m, exponent):
    # Exact finite checker only; trial division is not part of the theorem.
    r = exponent
    x = exponent
    fac = []
    p = 2
    while p * p <= x:
        if x % p == 0:
            fac.append(p)
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        fac.append(x)
    for p in fac:
        while r % p == 0 and pow(a, r // p, m) == 1:
            r //= p
    return r

def chain_split(N, E, a):
    g = gcd(a, N)
    if 1 < g < N:
        return g
    if g != 1:
        return None
    S = v2(E)
    for j in range(S + 1):
        d = gcd(pow(a, E // (2**j), N) - 1, N)
        if 1 < d < N:
            return d
    return None

P = primes_upto(80)
moduli = []
for k in range(2, 5):
    for ps in combinations(P, k):
        N = 1
        for p in ps:
            N *= p
        if N < 2_000_000:
            moduli.append(ps)

rho_checks = 0
character_checks = 0
conductor_cases = 0
mrs_large_cases = 0
profile_residual_cases = 0
for ps in moduli:
    N = 1
    E = 1
    for p in ps:
        N *= p
        E = lcm(E, p - 1)

    for a in range(2, min(N, 150)):
        if gcd(a, N) != 1:
            continue
        rhos = [v2(order_mod(a, p, p - 1)) for p in ps]
        got = chain_split(N, E, a)
        assert (got is not None) == (len(set(rhos)) > 1)
        rho_checks += 1

    layers = [v2(p - 1) for p in ps]
    if max(ps)**4 > N * E:
        # This is exactly alpha_1 > (1+tau)/4.
        mrs_large_cases += 1
    else:
        profile_residual_cases += 1
        if len(set(layers)) == 1:
            p0, p1 = ps[0], ps[1]
            assert p0 * p1 <= (E + 1)**2
            assert (p0 * p1)**len(ps) <= N**2
        else:
            q0 = min(p for p, s in zip(ps, layers) if s == max(layers))
            assert q0 <= E + 1
            assert q0**4 <= N * E

    if len(set(layers)) > 1:
        q = min(p for p, s in zip(ps, layers) if s == max(layers))
        assert q <= E + 1
        assert q <= N  # q <= rad(N)=N in this squarefree test
        lower = next(p for p, s in zip(ps, layers) if s < max(layers))
        seen = False
        for a in range(2, q):
            if gcd(a, N) != 1:
                continue
            if pow(a, (q - 1) // 2, q) == q - 1:
                assert v2(order_mod(a, q, q - 1)) > \
                       v2(order_mod(a, lower, lower - 1))
                assert chain_split(N, E, a) is not None
                character_checks += 1
                seen = True
                break
        assert seen
        conductor_cases += 1
    else:
        p, q = ps[0], ps[1]
        assert p * q <= (E + 1)**2
        assert p * q <= N  # pq <= rad(N)=N in this squarefree test
        seen = False
        for a in range(2, p * q):
            if gcd(a, N) != 1:
                continue
            lp = -1 if pow(a, (p - 1) // 2, p) == p - 1 else 1
            lq = -1 if pow(a, (q - 1) // 2, q) == q - 1 else 1
            if lp * lq == -1:
                assert chain_split(N, E, a) is not None
                character_checks += 1
                seen = True
                break
        assert seen
        conductor_cases += 1

# Prime-power blocks: a rho mismatch separates complete powers.
power_checks = 0
for p, q in [(3, 5), (3, 13), (5, 17), (7, 17), (11, 41)]:
    for kp, kq in product(range(1, 4), repeat=2):
        N = p**kp * q**kq
        ep = p**(kp - 1) * (p - 1)
        eq = q**(kq - 1) * (q - 1)
        E = lcm(ep, eq)
        for a in range(2, min(N, 100)):
            if gcd(a, N) != 1:
                continue
            rp = v2(order_mod(a, p**kp, ep))
            rq = v2(order_mod(a, q**kq, eq))
            d = chain_split(N, E, a)
            assert (d is not None) == (rp != rq)
            if d is not None:
                assert gcd(d, N // d) == 1
            power_checks += 1

# The short-multiple profile does not need squarefreeness. Check the
# exact integer inequalities for three distinct primes with multiplicity.
nonsquare_profile_checks = 0
for ps in combinations(primes_upto(30), 3):
    for exps in product(range(1, 3), repeat=3):
        N = 1
        E = 1
        rad = 1
        for p, e in zip(ps, exps):
            N *= p**e
            rad *= p
            E = lcm(E, p**(e - 1) * (p - 1))
        layers = [v2(p - 1) for p in ps]
        if max(ps)**4 <= N * E:
            if len(set(layers)) == 1:
                assert ps[0] * ps[1] <= (E + 1)**2
                assert (ps[0] * ps[1])**len(ps) <= rad**2 <= N**2
            else:
                q = min(p for p, s in zip(ps, layers) if s == max(layers))
                assert q <= E + 1
                assert q**4 <= N * E
        nonsquare_profile_checks += 1

print(f"squarefree moduli: {len(moduli)}")
print(f"rho/chain equivalence checks: {rho_checks}")
print(f"character-forced split witnesses: {character_checks}")
print(f"character conductor cases: {conductor_cases}")
print(f"MRS-large/profile-residual cases: {mrs_large_cases}/{profile_residual_cases}")
print(f"prime-power block checks: {power_checks}")
print(f"nonsquare profile checks: {nonsquare_profile_checks}")
print("PASS")
