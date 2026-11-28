#!/usr/bin/env python3
"""Exact finite checks for the two-odd-prime Carmichael-value reduction."""
from itertools import product
from math import gcd, isqrt, lcm, prod


def prime(n):
    if n in (2, 3):
        return True
    if n < 2 or gcd(n, 6) != 1:
        return False
    lim = isqrt(n)
    return all(n % d for a in range(5, lim + 1, 6)
               for d in (a, a + 2) if d <= lim)


def v(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def lambda_value(fac):
    parts = []
    for p, e in fac:
        parts.append(2**(e - 2) if p == 2 and e >= 3
                     else (p - 1) * p**(e - 1))
    return lcm(*parts)


def first_true(lo, hi, pred):
    """First true integer on inclusive [lo, hi], or hi+1."""
    left, right = lo, hi + 1
    while left < right:
        m = (left + right) // 2
        if pred(m):
            right = m
        else:
            left = m + 1
    return left


def convex_roots(f, lo, hi):
    if lo > hi:
        return []
    c = first_true(lo, hi - 1, lambda x: f(x + 1) >= f(x))
    x = first_true(lo, c, lambda x: f(x) <= 0)
    y = first_true(c, hi, lambda x: f(x) >= 0)
    return sorted({r for r in (x, y, y + 1)
                   if lo <= r <= hi and f(r) == 0})


def prime_power(n):
    if n < 2:
        return None
    for e in range(1, n.bit_length() + 1):
        p = first_true(2, n, lambda x: x**e >= n)
        if p <= n and p**e == n and prime(p):
            return (p, e)
    return None


def odd_factors(n, ell):
    if n == 1:
        return ()
    u = n // gcd(n, ell)
    if u <= 1:
        return None
    if prime(u):
        b = v(n, u)
        w = n // u**b
        if w == 1:
            fac = ((u, b),)
        else:
            g = prime_power(w)
            if g is None:
                return None
            fac = tuple(sorted((g, (u, b))))
        return fac if lambda_value(fac) == ell else None

    m = ell // (n // u)
    W = m * gcd(u - 1, m)
    for s in range(n.bit_length() + 1):
        def poly(x):
            return W * x**(s + 1) + x*x - (u + 1)*x + u
        for p in convex_roots(poly, 3, isqrt(u)):
            if u % p:
                continue
            q = u // p
            if p >= q or not prime(p) or not prime(q):
                continue
            a, b = v(n, p), v(n, q)
            fac = ((p, a), (q, b))
            if a and b and p**a * q**b == n and lambda_value(fac) == ell:
                return fac
    return None


def recover(N, ell):
    e = v(N, 2)
    n = N // 2**e
    z = v(ell, 2)
    odd = ell // 2**z
    for d in range(z + 1):
        fac = odd_factors(n, odd * 2**d) if e else odd_factors(n, ell)
        if fac is not None:
            full = (((2, e),) if e else ()) + fac
            if prod(p**r for p, r in full) == N and lambda_value(full) == ell:
                return full
        if not e:
            break
    return None


def reference(n):
    F = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            a = 0
            while n % p == 0:
                n //= p
                a += 1
            F.append((p, a))
        p += 1
    if n > 1:
        F.append((n, 1))
    return tuple(F)


def case_check(F):
    N = prod(p**e for p, e in F)
    ell = lambda_value(F)
    assert recover(N, ell) == F
    odd = tuple((p, a) for p, a in F if p != 2)
    masked = v(ell, 2) > v(lambda_value(odd), 2)
    if len(odd) < 2:
        return 0, masked
    (p, a), (q, b) = odd
    n = p**a * q**b
    L = lambda_value(odd)
    u = n // gcd(n, L)
    s = v(q - 1, p)
    if s >= a:
        assert u == q
        return 1, masked
    assert u == p*q
    t = (q - 1) // p**s
    m = L // (n // u)
    d = gcd(u - 1, m)
    assert m == lcm(t, p - 1)
    assert d == gcd(p - 1, t)
    assert m*d == (p - 1)*t
    assert (u-p)*(p-1) == m*d*p**(s+1)
    Z = d * sum(p**i for i in range(s + 1))
    assert u - m*Z == t + p and u//m - Z in (0, 1, 2)
    return (2 if s else 3), masked


def group_exponent(n):
    """Directly compute the lcm of all unit cycle lengths, for small n."""
    L = 1
    for a in range(1, n):
        if gcd(a, n) != 1:
            continue
        x, o = a, 1
        while x != 1:
            x = x*a % n
            o += 1
        L = lcm(L, o)
    return L


def main():
    counts = [0] * 4
    masked = 0
    for n in range(1, 16001):
        F = reference(n)
        if sum(p != 2 for p, _ in F) > 2:
            continue
        C, flag = case_check(F)
        counts[C] += 1
        masked += flag
    print("exhaustive 1..16000:", sum(counts), "inputs")
    print("at most one odd prime / prime radical due to cross /"
          " composite radical with cross / composite radical without cross:",
          *counts)
    print("strict two-adic masking cases:", masked)
    for n in range(1, 301):
        assert group_exponent(n) == lambda_value(reference(n))
    print("direct unit-group exponents:", 300)

    extras = (
        ((3, 4), (109, 2)),
        ((2, 18), (3, 9), (487, 4)),
        ((2, 25), (3, 5), (487, 2)),
        ((2, 100), (11, 20), (23, 17)),
        ((2, 15), (1000003, 5), (1000033, 7)),
    )
    for F in extras:
        assert all(prime(p) for p, _ in F)
        C, flag = case_check(F)
        n = prod(p**e for p, e in F)
        (p, _), (q, _) = F[-2:]
        print("structured:", n.bit_length(), "bits; cross valuation",
              v(q - 1, p), "branch", C, "masked", int(flag))

    root_checks = 0
    for W, U, s in product(range(1, 21), range(2, 51), range(7)):
        def f(x):
            return W*x**(s+1) + x*x - (U+1)*x + U
        assert convex_roots(f, 1, 12) == [x for x in range(1, 13) if f(x) == 0]
        root_checks += 1
    assert convex_roots(lambda x: (x-2)*(x-3), 1, 5) == [2, 3]
    assert convex_roots(lambda x: (x-2)**2, 1, 4) == [2]
    print("exact discrete root-search checks:", root_checks + 2)
    print("PASS")


if __name__ == "__main__":
    main()
