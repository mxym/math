"""Exact finite replay of the local identities used by ReverseTypeI.md."""
from fractions import Fraction as F
from math import gcd


def check(yes, msg):
    if not yes:
        raise ArithmeticError(msg)


def factors(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = 1
    return out


def phi(n):
    out = n
    for p in factors(n):
        out -= out // p
    return out


def mu(n):
    f = factors(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def divs(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def mangoldt_exponent(n, p):
    f = factors(n)
    return int(n > 1 and len(f) == 1 and p in f)


cnt = [0] * 4
for H in range(1, 18):
    for d in range(1, 16):
        for n in range(1, 58):
            got = sum((F(1, phi(e)) for e in divs(n) if mu(e) and gcd(e, H*d) == 1), F(0))
            check(got / (phi(H*d)*n) == F(1, phi(H*d*n)), 'totient opening')
            cnt[0] += 1
    for p in (2, 3, 5, 7, 11, 13, 17):
        # This average includes other prime factors of m, so isolate the p-local
        # multiplier exactly by opening only the p Euler factor.
        local = [F(p,p-1) if m%p==0 and H%p else F(1) for m in range(1,p+1)]
        check(local[-1] / sum(local) == (F(p,p*p-p+1) if H%p else F(1,p)), 'local weight')
        cnt[1] += 1

# Formal log vector: coordinate p of log t is v_p(t).
for r in range(2, 351):
    for V in (2, 3, 5, 11):
        for p in factors(r):
            ds = divs(r)
            def coord(t):
                return factors(t).get(p, 0)
            direct = sum(mu(a) * coord(r//a) for a in ds)
            short = sum(mu(a) * coord(r//a) for a in ds if a <= V)
            deb = sum(mu(a) * mangoldt_exponent(j,p) for a in ds if a <= V
                      for j in divs(r//a) if j <= V)
            long = sum(mu(a) * mangoldt_exponent(j,p) for a in ds if a > V
                       for j in divs(r//a) if j > V)
            tiny = mangoldt_exponent(r,p) if r <= V else 0
            check(direct == mangoldt_exponent(r,p) == tiny + short - deb + long, 'Vaughan formal log')
            cnt[2] += 1
for a in range(1,12):
    for m in range(1,15):
        for c in range(1,11):
            for y in range(1,200):
                check((y%(a*m)==0 and (y//(a*m))%c==0) == (y%(a*m*c)==0), 'physical product')
                cnt[3] += 1
print('Verified:', cnt, '(totient, prime-local, Vaughan, literal product)')
