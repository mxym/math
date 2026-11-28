#!/usr/bin/env python3
"""Finite arithmetic checks for the known-exponent grid obstruction."""
from itertools import combinations, product
from math import gcd, isqrt, lcm, prod


def prime(n):
    if n in (2, 3):
        return True
    if n < 2 or gcd(n, 6) != 1:
        return False
    limit = isqrt(n)
    return all(n % d for u in range(5, limit + 1, 6)
               for d in (u, u + 2) if d <= limit)


def progression_prime(Q, R, j):
    for t in range(1000):
        p = (j + t * R) * Q - 1
        if prime(p):
            return p
    raise AssertionError("small fixture search exhausted")


def prime_divisors(n):
    res = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            res.append(d)
            while n % d == 0:
                n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        res.append(n)
    return res


def valuation(n, ell):
    j = 0
    while n % ell == 0:
        n //= ell
        j += 1
    return j


def order(a, p, prime_factors):
    o = p - 1
    for r in prime_factors:
        while o % r == 0 and pow(a, o // r, p) == 1:
            o //= r
    assert pow(a, o, p) == 1
    assert all(pow(a, o // r, p) != 1 for r in prime_factors if o % r == 0)
    return o


def main():
    base_checks = order_checks = divisor_checks = negative_checks = 0
    for B in (3, 5, 7, 11, 13, 17, 19, 23):
        small = [s for s in range(2, B + 1) if prime(s)]
        Q = 4 * prod(small)
        ps = [progression_prime(Q, 8, j) for j in range(1, 9)]
        assert len(set(ps)) == 8
        assert all(p > B and p % Q == Q - 1 for p in ps)
        balanced = 0
        for p, q in combinations(ps, 2):
            N = p * q
            lam = lcm(p - 1, q - 1)
            balanced += p.bit_length() == q.bit_length()
            assert gcd(lam, prod(small)) == 2
            for b in range(1, B + 1):
                assert gcd(b, N) == 1 and pow(b, lam // 2, N) == 1
                base_checks += 1

        p = progression_prime(Q, 2, 1)
        q = progression_prime(Q, 2, 2)
        assert p % (2 * Q) == Q - 1 and q % (2 * Q) == 2 * Q - 1
        print(f"B={B} Q={Q} p={p} q={q} same-dyadic-band-pairs={balanced}")
        fp = prime_divisors(p - 1)
        fq = prime_divisors(q - 1)
        N = p * q
        lam = lcm(p - 1, q - 1)
        for b in range(1, B + 1):
            for r, fs in ((p, fp), (q, fq)):
                o = order(b, r, fs)
                assert gcd(o, prod(small)) == 1
                order_checks += 1

        if B <= 13:
            E = lam * prod(small) * 2**3 * 5**2
            all_D = [prod(ell**j for ell, j in zip(small, js))
                     for js in product(*(range(valuation(E, ell) + 1)
                                         for ell in small))]
            for b, D in product(range(1, B + 1), all_D):
                assert E % D == 0
                T = E // D
                assert gcd(pow(b, T, N) - 1, N) == N
                assert gcd(pow(-b, T, N) - 1, N) == (1 if T & 1 else N)
                divisor_checks += 1
                negative_checks += 1

    N = 9239 * 55439
    fermat = pow(2, N - 1, N)
    assert fermat == 419026630 and fermat != 1
    print(f"ordinary-Fermat-negative-control N={N} base=2 residue={fermat}")

    p, q, b, r, B = 23, 47, 2, 23, 3
    N = p * q
    o = lcm(order(b, p, prime_divisors(p - 1)),
            order(b, q, prime_divisors(q - 1)))
    g = gcd(pow(b, o // r, N) - 1, N)
    assert o % r == 0 and r > B and 1 < g < N
    assert gcd(pow(b, lcm(p - 1, q - 1) // r, N) - 1, N) == g
    print(f"out-of-grid-negative-control N={N} base={b} r={r} order={o} gcd={g}")
    assert (base_checks, order_checks, divisor_checks, negative_checks) == (2744, 196, 8052, 8052)
    print(f"PASS generator={base_checks} local-order={order_checks}"
          f" positive-gcd={divisor_checks} negative-gcd={negative_checks}")


if __name__ == "__main__":
    main()
