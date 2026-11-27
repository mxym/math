"""Independent exact Fourier counts and tiny direct checks."""

from itertools import combinations, product
from collections import Counter
from fractions import Fraction as Q
from math import comb, isqrt

n, k, m, N = 54, 3, 55, 18
P, R = 2147483647, 100000000003


def c(a, b):
    return comb(a, b) if 0 <= b <= a else 0


def sieve_prime_checks():
    bound = isqrt(R)
    s = bytearray(b"\1") * (bound + 1)
    s[0] = s[1] = 0
    for a in range(2, isqrt(bound) + 1):
        if s[a]:
            s[a*a::a] = b"\0" * ((bound - a*a) // a + 1)
    for p in (P, R):
        assert all(p % d for d in range(2, isqrt(p) + 1) if s[d])


def shell_fourier(p, dimension, weight, steps):
    # Integer transform of the unnormalized weight sphere: each nonzero
    # frequency coordinate contributes -1 instead of p-1.
    V = comb(dimension, weight) * (p - 1)**weight
    F = [
        sum(c(j, a) * c(dimension - j, weight - a) * (-1)**a * (p - 1)**(weight - a)
            for a in range(weight + 1))
        for j in range(dimension + 1)
    ]
    multiplicity = [comb(dimension, j) * (p - 1)**j for j in range(dimension + 1)]
    assert F[0] == V and sum(multiplicity) == p**dimension
    def hit(step):
        count, residue = divmod(sum(z*f**step for z, f in zip(multiplicity, F)), p**dimension)
        assert residue == 0 and 0 <= count <= V**step
        return Q(count, V**step)
    return [hit(step) for step in range(steps + 1)]


def direct_convolution(p, n, k, jmax):
    rows = []
    for support in combinations(range(n), k):
        for nonzero in product(range(1, p), repeat=k):
            r = [0] * n
            for i, x in zip(support, nonzero):
                r[i] = x
            rows.append(tuple(r))
    zero = (0,) * n
    hist = Counter({zero: 1})
    hits = [Q(1)]
    for j in range(1, jmax + 1):
        next_hist = Counter()
        for x, value in hist.items():
            for row in rows:
                next_hist[tuple((a + b) % p for a, b in zip(x, row))] += value
        hist = next_hist
        hits.append(Q(hist[zero], len(rows)**j))
    return hits


def contribution(p, j):
    # Closed form, independent of the recurrence in the other checker.
    a = (1 + Q((-1)**j, (p - 1)**(j - 1))) / p
    return comb(m, j) * (p - 1)**j * a**k / comb(n, k)**(j - 1)


def cumulative(p, lines):
    hits = shell_fourier(p, n, k, 6)
    terms = [Q(comb(m, j) * (p - 1)**(j - lines)) * hits[j] for j in range(1, 7)]
    assert terms[0] == 0
    return {d: sum(terms[:d-1]) for d in range(2, 8)}


def main():
    sieve_prime_checks()
    cases = [(2, 3, 2), (3, 3, 3), (3, 4, 2), (5, 3, 2)]
    for p, dim, weight in cases:
        assert direct_convolution(p, dim, weight, 5) == shell_fourier(p, dim, weight, 5)
    print("independent prime sieve and 4 tiny direct convolution/Fourier cases PASS")

    u = shell_fourier(2, N, 1, 6)
    def B(d):
        return sum(comb(m, j) * u[j]**k for j in range(1, d))
    b, c = B(6), B(7)
    assert b.denominator - 2*b.numerator == 310951
    assert 2*c.numerator - c.denominator == 126892944355522

    raw, proj = cumulative(P, False), cumulative(R, True)
    assert raw[4] < Q(1, 10000) < Q(1, 2) < 47 < contribution(P, 4) <= raw[5] - raw[4]
    assert proj[5] < Q(1, 10000000) < Q(1, 2) < Q(9, 10) < contribution(R, 5)/(R-1) <= proj[6] - proj[5]
    assert Q(1, 2) < cumulative(R, False)[5]
    assert cumulative(2, False)[6] < Q(1, 2) < cumulative(P, True)[7]
    print("independent exact crossings: binary 6, p=2147483647 raw 4, p=100000000003 lines 5")
    print("PASS: additive-character counts")


if __name__ == "__main__":
    main()
