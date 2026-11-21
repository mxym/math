"""Exact finite controls for the odd-valuation path theorem; run with Python 3."""
from itertools import permutations
from math import gcd, isqrt


def check(condition, why):
    if not condition:
        raise ValueError(why)


def factor(n):
    ans = {}
    for d in range(2, isqrt(n) + 1):
        while n % d == 0:
            n //= d
            ans[d] = ans.get(d, 0) + 1
    if n > 1:
        ans[n] = 1
    return ans


def prime(n):
    return n >= 2 and factor(n) == {n: 1}


def odd(N, x):
    return {q for q, e in factor(N - x).items() if e % 2}


def jacbit(N, x):
    residue = pow(N % x, (x - 1) // 2, x)
    check(residue in (1, x - 1), ("Euler criterion", N, x))
    return int(residue == x - 1)


def physical():
    rows = 0
    for N in range(6, 2001, 4):
        for x in range(3, N - 1, 2):
            if not prime(x) or gcd(x, N) != 1:
                continue
            S = odd(N, x)
            check(all(y != x and prime(y) and gcd(y, N) == 1 for y in S), "unit edges")
            eps = int(x % 4 == 3)
            check((sum(y % 4 == 3 for y in S) % 2) == eps, ("epsilon", N, x))
            check((jacbit(N, x) ^ (sum(jacbit(N, y) for y in S) % 2)) == eps,
                  ("lambda", N, x))
            rows += 1
    check([odd(514, p) for p in (3, 7, 73)] == [{7, 73}, {3}, set()], "514")
    check([odd(852, p) for p in (5, 7)] == [{7}, {5}], "852")
    check(prime(13) and prime(839) and 13 + 839 == 852, "represented")
    print("physical rows", rows, "fixtures 514,852")


def canonical_cycles(n):
    cycles = []
    for length in range(2, n + 1):
        for c in permutations(range(n), length):
            if c[0] == min(c):
                cycles.append((set(c), {(c[i-1], c[i]) for i in range(length)}))
    return cycles


def graph_control():
    total = double = no_disjoint = 0
    for n in range(1, 5):
        edges = [(i, j) for i in range(n) for j in range(n) if i != j]
        cycles = canonical_cycles(n)
        perms = list(permutations(range(n)))
        for mask in range(1 << len(edges)):
            adj = {e for b, e in enumerate(edges) if mask >> b & 1}
            # Leibniz polynomial over F2, indexed by degree, no cycle routines here.
            char = 0
            for perm in perms:
                if all(i == j or (i, j) in adj for i, j in enumerate(perm)):
                    char ^= 1 << sum(i == j for i, j in enumerate(perm))
            total += 1
            if char.bit_count() % 2 or sum((char >> i) & 1 for i in range(1, n + 1, 2)) % 2:
                continue
            double += 1
            hits = [verts for verts, ce in cycles if ce <= adj]
            if not any(u.isdisjoint(v) for u in hits for v in hits):
                no_disjoint += 1
                check(any(len(u) % 2 == 0 for u in hits), ("graph", n, mask))
    print("loopless graphs", total, "double root", double, "no disjoint cycles", no_disjoint)


if __name__ == "__main__":
    physical()
    graph_control()
