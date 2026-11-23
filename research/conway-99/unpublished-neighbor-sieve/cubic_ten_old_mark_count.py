"""Count labelled induced subgraphs through six vertices as affine functions of P."""
from collections import Counter
from functools import cache
from itertools import combinations
from math import factorial, perm


@cache
def edges(n):
    return tuple(combinations(range(n), 2))


@cache
def partitions(n):
    if n == 0:
        return ((),)
    return tuple(part + (block,) for part in partitions(n - 1)
                 for block in range(max(part, default=-1) + 2))


def quotient(n, mask, part):
    size = max(part, default=-1) + 1
    bits = 0
    for i, (u, v) in enumerate(edges(n)):
        if mask & (1 << i):
            a, b = sorted((part[u], part[v]))
            if a == b:
                return None
            bits |= 1 << edges(size).index((a, b))
    return size, bits


def census(prisms):
    @cache
    def noninjective(n, mask):
        total = 0
        for part in partitions(n):
            if len(set(part)) < n:
                smaller = quotient(n, mask, part)
                if smaller is not None:
                    total += injective(*smaller)
        return total

    @cache
    def hom(n, mask):
        if n == 0:
            return 1
        adj = [set() for _ in range(n)]
        for i, (u, v) in enumerate(edges(n)):
            if mask & (1 << i):
                adj[u].add(v)
                adj[v].add(u)
        root = min(range(n), key=lambda u: len(adj[u]))
        degree = len(adj[root])
        if degree >= 3:
            prism = (n == 6 and all(len(row) == 3 for row in adj)
                     and any(adj[u] & adj[v] for u in range(n) for v in adj[u]))
            return noninjective(n, mask) + (12 * prisms if prism else 0)
        points = [u for u in range(n) if u != root]
        sub = sum(1 << i for i, (u, v) in enumerate(edges(n - 1))
                  if points[v] in adj[points[u]])
        base = hom(n - 1, sub)
        if degree == 0:
            return 99 * base
        if degree == 1:
            return 14 * base
        u, v = sorted(points.index(p) for p in adj[root])
        add_edge = 1 << edges(n - 1).index((u, v))
        part = tuple(u if p == v else p - int(p > v) for p in range(n - 1))
        merged = quotient(n - 1, sub, part)
        diagonal = hom(*merged) if merged is not None else 0
        return 2 * base - hom(n - 1, sub | add_edge) + 12 * diagonal

    @cache
    def injective(n, mask):
        return hom(n, mask) - noninjective(n, mask)

    @cache
    def induced(n):
        values = [injective(n, mask) for mask in range(1 << len(edges(n)))]
        for i in range(len(edges(n))):
            for mask in range(len(values)):
                if not mask & (1 << i):
                    values[mask] -= values[mask | (1 << i)]
        assert sum(values) == perm(99, n)
        return values

    out = {}
    for n in (3, 5):
        plus = (n + 1) // 2
        count = Counter()
        for mask, value in enumerate(induced(n)):
            eta = sum((1 if (i < plus) == (j < plus) else -1)
                      for bit, (i, j) in enumerate(edges(n)) if mask >> bit & 1)
            count[21 * n - 14 * eta + 2] += value
        div = factorial(plus) * factorial(n - plus)
        assert all(v % div == 0 for v in count.values())
        out[n] = {k: v // div for k, v in count.items()}
    assert (out[3][79], out[5][79]) == (100485, 29259846)
    assert (out[3][51], out[5][51]) == (49896, 55440)
    return out

if __name__ == '__main__':
    print({n: (x[51], x[79]) for n, x in census(0).items()})
