#!/usr/bin/env python3
"""Integer norm / modular polynomial route; no finite-field element enumeration."""
from itertools import combinations
from math import comb, gcd, isqrt


def modpoly(a, b, p):
    a = [x % p for x in a]
    while a and a[-1] == 0:
        a.pop()
    lead_inv = pow(b[-1], -1, p)
    while len(a) >= len(b):
        f, s = a[-1] * lead_inv % p, len(a) - len(b)
        for j, x in enumerate(b):
            a[s+j] = (a[s+j] - f*x) % p
        while a and a[-1] == 0:
            a.pop()
    return a


def degree_gcd(a, b, p):
    while b:
        a, b = b, modpoly(a, b, p)
    return len(a) - 1


def bareiss(m):
    a = [list(r) for r in m]
    sign, previous = 1, 1
    for i in range(len(a)-1):
        if not a[i][i]:
            j = next((j for j in range(i+1, len(a)) if a[j][i]), None)
            if j is None:
                return 0
            a[i], a[j], sign = a[j], a[i], -sign
        for j in range(i+1, len(a)):
            for k in range(i+1, len(a)):
                v = a[j][k]*a[i][i] - a[j][i]*a[i][k]
                assert v % previous == 0
                a[j][k] = v // previous
        previous = a[i][i]
    return sign * a[-1][-1]


def norm(m):
    # Multiplication matrix of B_m on Z[T]/(T^(m/2)+1),
    # in the basis 1,T,...,T^(m/2-1).
    r = m//2
    a = [[0]*r for _ in range(r)]
    for j in range(r):
        for i in range(r+1):
            flip, k = divmod(i+j, r)
            a[k][j] += (-1)**flip * comb(m, 2*i)
    return bareiss(a)


def degrees(n, p):
    m = n//2
    monic = [1] + [0]*(m//2-1) + [1]
    b = [comb(m, 2*j) % p for j in range(m//2+1)]
    fourth = degree_gcd(monic, b, p)
    subtraction = degree_gcd([1] + [0]*(m-1) + [1],
                             [p-1, p-2, 1], p)
    return fourth, subtraction


def prime_power(q):
    for p in range(2, isqrt(q)+1):
        if q % p == 0:
            t = q
            while t % p == 0:
                t //= p
            return p if t == 1 else None
    return q if q > 1 else None


def exhaustive_support_shapes():
    # Raw stable triples satisfying all necessary gcd/parity conditions.
    # Compare support sets, not just their nonemptiness, across both parities.
    modulus_cases = checked_supports = 0
    for n in range(5, 38):
        all3 = list(combinations(range(n), 3))
        for a in range(2, n-1):
            if gcd(a, n) != 1:
                continue
            modulus_cases += 1
            actual = set()
            for t in all3:
                if tuple(sorted(a*x % n for x in t)) != t:
                    continue
                if n % 2 == 0 and len({x % 2 for x in t}) == 1:
                    continue
                if any(gcd(x-y, n) > 2 for x, y in combinations(t, 2)):
                    continue
                actual.add(t)
            expected = set()
            units = [u for u in range(n) if gcd(u, n) == 1]
            if n % 8 == 0 and a == n//2-1:
                expected = {tuple(sorted((b, (b+u) % n, (b+a*u) % n)))
                            for b in (0, n//2) for u in units}
                assert len(expected) == len(units)
            elif n % 2 and gcd(a-1, n) == 1 and (a*a+a+1) % n == 0:
                expected = {tuple(sorted((u, a*u % n, a*a*u % n)))
                            for u in units}
                assert len(expected)*3 == len(units)
            assert actual == expected, (n, a, actual, expected)
            checked_supports += len(actual)
    print(f"Stable support sieve: {modulus_cases} (n,q mod n) cases,"
          f" {checked_supports} survivors; exact set equality.")


def main():
    exhaustive_support_shapes()
    ns = [4, 8, 12, 16]
    ds = [36, 2**4*7**4*17**2, 2**6*3**12*5**4*11**6,
          2**8*47**4*79**4*97**4*577**2]
    assert [norm(m) for m in ns] == ds
    print("Exact integer norms D_m:", list(zip(ns, ds)))

    remaining = [q for q in range(11, 62, 12) if prime_power(q)]
    assert remaining == [11, 23, 47, 59]
    assert (62+1)**2 > 64*62 and 2*62-62 > 0
    print("Index 3 exact report (q,n,d,e,singular minors,curve points):")
    expected = [(11, 8, 0, 0, 0, 0), (23, 16, 0, 0, 0, 0),
                (47, 32, 4, 0, 128, 72), (59, 40, 6, 2, 200, 108)]
    out = []
    for q in remaining:
        n = 2*(q+1)//3
        d, e = degrees(n, prime_power(q))
        assert (norm(n//2) % q != 0) == (d == 0)
        row = q, n, d, e, n//2*(2*d-e), 18*d
        out.append(row)
        print(row)
    assert out == expected
    assert degrees(8, 3)[0] > 0 and degrees(16, 7)[0] > 0
    print("Prime-power negative controls n=8,q=27 and n=16,q=343: PASS.")


if __name__ == "__main__":
    main()
