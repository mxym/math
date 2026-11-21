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

    result = {}
    for plus, minus in ((1, 1), (2, 2), (3, 0), (4, 1), (3, 3), (6, 0)):
        n = plus + minus
        counts = Counter()
        for mask, multiplicity in enumerate(induced(n)):
            if not multiplicity:
                continue
            internal = cross = 0
            for i, (a, b) in enumerate(edges(n)):
                if mask & (1 << i):
                    if (a < plus) == (b < plus):
                        internal += 1
                    else:
                        cross += 1
            # For (4,1) count only isolated negative sites.
            if (plus, minus) == (4, 1) and cross:
                continue
            norm = 3*n + (plus-minus)**2//9 - 2*(internal-cross)
            counts[norm] += multiplicity
        divisor = factorial(plus) * factorial(minus)
        assert all(v % divisor == 0 for v in counts.values())
        result[plus, minus] = tuple(counts[k] // divisor for k in (4, 6, 8))
    return result


def main():
    for p in (0, 1):
        marks = census(p)
        baseline = [sum((2 if a != b else 1) * marks[a, b][k]
                        for a, b in ((1, 1), (2, 2), (3, 0), (4, 1)))
                    for k in range(3)]
        assert baseline == [462, 24948, 1398474]
        assert marks[3, 3][1:] == (7392 - 2*p, 765072 + 18*p)
        assert marks[6, 0][1:] == (20790 - 9*p, 831600 + 36*p)
        print(p, baseline, marks[3, 3][1:], marks[6, 0][1:], flush=True)


if __name__ == "__main__":
    main()
