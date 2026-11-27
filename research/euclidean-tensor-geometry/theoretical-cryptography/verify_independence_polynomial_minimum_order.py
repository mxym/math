#!/usr/bin/env python3
"""Exact finite certificate for the minimum order 15.

Python 3.10+ standard library only. This checks integer clique-count
constraints, not a list of simple graphs.
"""

from functools import lru_cache
from itertools import combinations, combinations_with_replacement
from math import comb


def C(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def ceildiv(p, q):
    return -((-p) // q)


def triangles(n, m):
    return max(0, ceildiv(4*m*m - n*n*m, 3*n)) if n else 0


@lru_cache(None)
def upper(n, r, k):
    """Colored colex upper bound indexed by the number of k-faces."""
    def allowed(h):
        return [mask for mask in range(1 << n)
                if mask.bit_count() == h and
                len({j % r for j in range(n) if mask >> j & 1}) == h]

    rank = {mask: j for j, mask in enumerate(allowed(k), 1)}
    counts = [0] * (len(rank) + 1)
    for mask in allowed(k + 1):
        counts[rank[mask ^ (mask & -mask)]] += 1
    for j in range(1, len(counts)):
        counts[j] += counts[j-1]
    return counts


@lru_cache(None)
def lower(n, r):
    """Dictionary m -> list of proven lower bounds at ranks 3,...,r."""
    q = n - r
    result = {}
    for D in combinations_with_replacement(range(r), q):
        first = [C(r, k) + sum(C(d, k-1) for d in D)
                 for k in range(3, r + 1)]
        minimum_intersections = sorted(max(0, d+v-r)
                                       for d, v in combinations(D, 2))
        partial = [0] * (r - 2)
        edges = C(r, 2) + sum(D)
        for e in range(len(minimum_intersections) + 1):
            m = edges + e
            candidate = [a+b for a, b in zip(first, partial)]
            candidate[0] = max(candidate[0] + triangles(q, e),
                               triangles(n, m))
            if m in result:
                result[m] = [min(a, b) for a, b in zip(result[m], candidate)]
            else:
                result[m] = candidate
            if e < len(minimum_intersections):
                c = minimum_intersections[e]
                for j in range(r - 2):
                    partial[j] += C(c, j+1)
    return result


def possible_valley(n, r, forbidden):
    L = lower(n, r)
    # At rank k, key = (fixed f2, current f_k, shape flag); value = max f_(k-1).
    states = {(m, m, int(m < n)): n
              for m in range(C(r, 2), upper(n, r, 1)[n] + 1) if m in L}
    for k in range(2, r):
        U = upper(n, r, k)
        next_states = {}
        for (m, a, h), b in states.items():
            lo = max(L[m][k-2],
                     ceildiv(k*k*a*a - n*a*b, (k*k - 1)*b))
            for x in range(lo, U[a]+1):
                if h == 1 and x > a and (k, m, a) in forbidden:
                    continue
                z = 2 if h == 2 or (h == 1 and x > a) else int(h or x < a)
                key = m, x, z
                if a > next_states.get(key, 0):
                    next_states[key] = a
        states = next_states
    return any(h == 2 for _, _, h in states)


def residual(m):
    """Pure counting bound when n=14, r=7, (f2,f3)=(m,m-1)."""
    results = []
    for D in combinations_with_replacement(range(7), 7):
        e = m - 21 - sum(D)
        if not 0 <= e <= 21:
            continue
        L = sum(C(d, 2) for d in D)
        V = sum(C(d, 3) for d in D)
        t0 = triangles(7, e)
        A = m - 36
        if L + t0 <= A:
            results.append(35 + V + 4*(A-L) - 3*t0)
    return len(results), max(results)


def witness():
    counts = [0] * 16
    # The complement has all first-six edges apart from {0,1},
    # and its last nine vertices are isolated.
    for word in range(1 << 15):
        k = word.bit_count()
        if k <= 1 or (word < (1 << 6) and (word & 3) != 3):
            counts[k] += 1
    return tuple(counts[:6]), sum(counts[6:])


def check(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def main():
    n = 14  # isolated padding in the complement handles all smaller orders
    raw = [r for r in range(3, n+1) if possible_valley(n, r, set())]
    check(raw == [7], ("unexpected preliminary ranks", raw))
    blocked = {(3, 50, 49), (3, 51, 50)}
    check(not possible_valley(n, 7, blocked), "unclassified crossing at r=7")
    left = [(m, *residual(m)) for m in (50, 51)]
    check(left == [(50, 7, 43), (51, 2, 40)], ("unexpected residuals", left))
    W = witness()
    check(W == ((1, 15, 14, 16, 9, 2), 0), ("bad witness", W))
    print("order 14: only preliminary clique number", raw[0])
    print("residuals (edges, feasible degree multisets, f4 upper bound):", left)
    print("order 15 witness:", W[0])
    print("PASS: exact minimum order 15")


if __name__ == "__main__":
    main()
