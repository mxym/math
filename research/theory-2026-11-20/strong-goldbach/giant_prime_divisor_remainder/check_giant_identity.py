#!/usr/bin/env python3
"""Finite exact checks of the literal mark and quotient formulae, not the analytic estimates."""
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt


def check(condition, label, data):
    if not condition:
        raise SystemExit((label, data))


def factor(n):
    f = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def phi(n):
    out = n
    for p in factor(n):
        out = (out // p) * (p - 1)
    return out


def mobius(n):
    f = factor(n)
    return 0 if any(a > 1 for a in f.values()) else (-1)**len(f)


def divisors(n):
    front = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return front + [n // d for d in reversed(front) if d * d != n]


def mark(d):
    f = factor(d)
    return next(iter(f)) if len(f) == 1 else None


def linear_sum(rows):
    ret = Counter()
    for prime, signed_count in rows:
        if prime is not None:
            ret[prime] += signed_count
    return {prime: c for prime, c in ret.items() if c}


def finite_identities():
    cnt_mark = cnt_cut = cnt_exact = cnt_two = 0
    for y in range(3, 401):
        div = divisors(y)
        f = factor(y)
        for B in (Fraction(1), Fraction(5, 2), Fraction(3), Fraction(9, 2),
                  Fraction(y, 9), Fraction(y, 7), Fraction(y, 3), Fraction(2*y, 3)):
            if not 1 <= B < y:
                continue
            for U in (Fraction(1), Fraction(2), Fraction(7, 2),
                      min(Fraction(13), B), Fraction(B, 2)):
                if not 1 <= U <= B:
                    continue
                actual = linear_sum((p, a * mobius(y // b))
                                    for b in div if b <= B
                                    for p, a in factor(b).items())
                low_all = linear_sum((mark(d), mobius(y // b))
                                     for b in div for d in divisors(b) if d <= U)
                check(not low_all, "vanishing complete small mark", (y, B, U))
                cnt_mark += 1
                low_upper = [(mark(d), -mobius(n)) for n in div if n * B < y
                             for d in div if d <= U and y % (d * n) == 0]
                low_prefix = linear_sum((mark(d), mobius(y // b)) for b in div if b <= B
                                        for d in divisors(b) if d <= U)
                check(low_prefix == linear_sum(low_upper), "small mark switch", (y, B, U))
                high = [(mark(d), -sum(mobius(n) for n in divisors(y // d) if n * B < y))
                        for d in div if U < d <= B]
                check(actual == linear_sum(low_upper + high), "full cutoff switch", (y, B, U))
                cnt_cut += 1
                if (y / B).denominator == 1 and y % (y / B).numerator == 0:
                    cnt_exact += 1
                giants = [p for p in f if p > U and p >= y / B]
                if len(giants) == 2 and U**3 > y:
                    r, s = giants
                    check(all((y // (r * s)) % n == 0
                              for n in divisors(y // r) if n * B < y),
                          "other giant cannot occur in short divisor", (y, B, U, r, s))
                    cnt_two += 1
    print(f"PASS {cnt_mark} complete marks, {cnt_cut} cutoff switches,"
          f" {cnt_exact} strict endpoint fixtures, {cnt_two} two-giant short masks")


def totient_cases():
    cases = 0
    for target in range(2, 70, 2):
        for d in range(1, 42):
            for n in range(1, 81):
                actual = Fraction(phi(d) * n * mobius(n), phi(d*n)) * (gcd(n, target) == 1)
                expected = Fraction(mobius(n) * (gcd(n, target) == 1))
                for p in factor(n):
                    if d % p:
                        expected *= Fraction(p, p-1)
                check(expected == actual, "signed Euler factor", (target, d, n))
                cases += 1
    print(f"PASS {cases} unit-masked totient coefficients")


if __name__ == "__main__":
    finite_identities()
    totient_cases()
