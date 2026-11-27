"""Exact shell-transition check, fixed abstract random-code examples."""

from fractions import Fraction as Q
from math import comb, isqrt

N, n, m, k = 18, 54, 55, 3
P, R = 2147483647, 100000000003


def odd_divisibility(p):
    assert p > 2 and p % 2
    assert all(p % d for d in range(3, isqrt(p) + 1, 2))


def binary_walk(length, steps):
    # Count ordered sequences by the number of odd bins after each throw.
    hist = [1] + [0] * length
    out = [Q(1)]
    for step in range(1, steps + 1):
        new = [0] * (length + 1)
        for w, count in enumerate(hist):
            if w:
                new[w - 1] += count * w
            if w < length:
                new[w + 1] += count * (length - w)
        hist = new
        assert sum(hist) == length**step
        out.append(Q(hist[0], length**step))
    return out


def shell_steps(p, steps):
    # Distribution counts for one current vector of weight a;
    # these are the numbers of choices of the next row.
    row_count = comb(n, k) * (p - 1)**k
    transition = [[0] * (n + 1) for _ in range(n + 1)]
    for a in range(n + 1):
        for r in range(max(0, k - n + a), min(a, k) + 1):
            support_choices = comb(a, r) * comb(n - a, k - r)
            for z in range(r + 1):
                b = a + k - r - z
                transition[a][b] += (
                    support_choices * comb(r, z) * (p - 2)**(r - z) * (p - 1)**(k - r)
                )
        assert sum(transition[a]) == row_count
    hits = [Q(1)]
    hist = [1] + [0] * n
    for j in range(1, steps + 1):
        new = [0] * (n + 1)
        for a, count in enumerate(hist):
            if count:
                for b, choices in enumerate(transition[a]):
                    new[b] += count * choices
        hist = new
        assert sum(hist) == row_count**j
        hits.append(Q(hist[0], row_count**j))
    return hits


def terms(p):
    return [comb(m, j) * (p - 1)**j * x for j, x in enumerate(shell_steps(p, 6))]


def lower_term(p, j):
    # Independent recursion for the scalar return law.
    a = Q(0)
    for _ in range(1, j):
        a = (1 - a) / (p - 1)
    return Q(comb(m, j), comb(n, k)**(j - 1)) * (p - 1)**j * a**k


def main():
    for p in (P, R):
        odd_divisibility(p)
    print("primes: odd trial divisibility PASS for 2147483647 and 100000000003")

    u = binary_walk(N, 6)
    assert u[1] == u[3] == u[5] == 0
    assert u[2] == Q(1, N)
    assert u[4] == Q(3*N - 2, N**3)
    assert u[6] == Q(15*N*N - 30*N + 16, N**5)
    b6 = sum(comb(m, j) * u[j]**k for j in range(1, 6))
    b7 = b6 + comb(m, 6) * u[6]**k
    assert b6 == Q(21367885, 43046721) < Q(1, 2)
    assert b7 == Q(154953641997605, 183014339639688) > Q(1, 2)
    print(f"binary occupancy: B(6)={b6}, B(7)={b7}, cutoff=6")

    card = comb(n, k)
    analytic4 = Q(comb(m, 2), P - 1) + comb(m, 3) * (Q(1, card**2) + Q(1, P - 1))
    analytic5line = (Q(comb(m, 2), (R-1)**2) + Q(comb(m, 3), R-1)
                     + comb(m, 4) * (Q(1, card**3) + Q(1, R-1)))
    assert analytic4 < Q(1, 10000) and analytic5line < Q(1, 100000)
    a = terms(P)
    la = lower_term(P, 4)
    assert a[1] == 0 and 47 < la <= a[4] < 49
    assert 0 < sum(a[1:4]) < Q(1, 10000)
    assert 0 < a[4] - la < Q(1, 10000)
    print("raw at p=2147483647: S(4)<1/10000, identical supports alone >47 at weight 4; cutoff=4")

    b = terms(R)
    lb = lower_term(R, 5) / (R - 1)
    assert b[1] == 0 and Q(9, 10) < lb <= b[5] / (R - 1) < 1
    assert 0 < sum(b[1:5]) / (R - 1) < Q(1, 10000000)
    assert 0 < b[5] / (R - 1) - lb < Q(1, 1000000)
    print("lines at p=100000000003: S(5)/(p-1)<1/10000000, identical supports alone >9/10 at weight 5; cutoff=5")

    assert sum(terms(2)[1:6]) < Q(1, 2)
    assert sum(terms(3)[1:7]) < Q(1, 2)
    assert sum(a[1:6]) / (P - 1) < Q(1, 2) < sum(a[1:7]) / (P - 1)
    print("controls: exact-weight binary reaches cutoff 6; p=3 raw reaches cutoff 7; projectivizing the smaller prime restores cutoff 6 for that instance")
    print("PASS: integer transition counts")


if __name__ == "__main__":
    main()
