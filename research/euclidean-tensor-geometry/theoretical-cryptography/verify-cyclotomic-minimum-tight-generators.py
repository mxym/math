#!/usr/bin/env python3
"""Exact checks for trace normalization and the signed 3-by-5 primitive block."""
from itertools import combinations, product
from math import gcd, prod

def ramanujan(modulus, difference):
    # Direct roots-of-unity inclusion-exclusion by divisors.
    def mu(n):
        primes = 0
        f = 2
        while f * f <= n:
            if n % f == 0:
                n //= f
                primes += 1
                if n % f == 0:
                    return 0
            f += 1
        return (-1) ** (primes + (n > 1))
    return sum(t * mu(modulus // t)
               for t in range(1, gcd(modulus, difference) + 1)
               if gcd(modulus, difference) % t == 0)

def trace_check():
    seen = 0
    for a, ep, eq, p, q in [
        (0, 0, 0, 3, 5), (1, 0, 0, 3, 5), (3, 0, 0, 3, 5),
        (0, 1, 0, 3, 5), (0, 2, 0, 3, 5), (2, 0, 2, 3, 5),
        (0, 1, 1, 3, 5), (1, 1, 1, 3, 7), (3, 1, 1, 5, 7),
        (2, 2, 1, 3, 5), (0, 1, 2, 3, 5)]:
        n = 2**a * p**ep * q**eq
        b2 = 2**max(a-1, 0)
        b = b2 * p**max(ep-1, 0) * q**max(eq-1, 0)
        axes = [(s, e) for s, e in ((p, ep), (q, eq)) if e]
        tags = list(product(range(b2), *[range(s**(e-1)) for s, e in axes]))
        labels = list(product(*[range(s-1) for s, e in axes]))
        indices = [(u, v) for u in tags for v in labels]
        exponents = []
        for u, v in indices:
            x = (n // 2**a) * u[0]
            x += sum((n // s**e) * (i + s**(e-1) * j)
                     for (s, e), i, j in zip(axes, u[1:], v))
            exponents.append(x % n)
        assert len(tags) == b
        assert len(set(exponents)) == len(indices)
        by_dif = {t: ramanujan(n, t) for t in range(n)}
        for (u, v), x in zip(indices, exponents):
            for (uu, vv), xx in zip(indices, exponents):
                target = 0
                if u == uu:
                    target = b * prod(s * (i == j) - 1
                                      for (s, _), i, j in zip(axes, v, vv))
                assert by_dif[(x-xx) % n] == target
                seen += 1
        # CRT list of all roots, quotienting by antipodal pairs if even.
        roots = set()
        mod = n if a == 0 else n//2
        for u in tags:
            for v in product(*[range(s) for s, e in axes]):
                x = (n // 2**a) * u[0]
                x += sum((n // s**e) * (i + s**(e-1) * j)
                         for (s, e), i, j in zip(axes, u[1:], v))
                roots.add(x % mod)
        assert len(roots) == mod == b * prod(s for s, e in axes)
    return seen

def add_basis(x, pivots):
    for y in pivots:
        x = min(x, x ^ y)
    return tuple(sorted((*pivots, x), reverse=True)) if x else None

def four_pattern_check():
    masks = tuple(range(1, 16))
    patterns = []
    for v in product(range(3), repeat=5):
        sizes = dict(zip((15, 7, 11, 13, 14), v))
        sizes.update((x, 4 if x.bit_count() == 1 else 2)
                     for x in masks if x.bit_count() <= 2)
        mult = {x: sum((-1)**((y^x).bit_count()) * sizes[y]
                       for y in masks if x & y == x) for x in masks}
        if min(mult.values()) < 0:
            continue
        cols = [x for x in masks for _ in range(mult[x])]
        first = tuple(sum(1 << j for j, x in enumerate(cols) if x >> i & 1)
                      for i in range(4))
        pivots = ()
        for x in first:
            pivots = add_basis(x, pivots)
            if pivots is None:
                break
        # The four triple counts can be sorted by relabeling the row pairs.
        if pivots is not None and tuple(sorted(v[1:])) == v[1:]:
            patterns.append((v, len(cols), first, pivots))
    assert [(v, s) for v, s, _, _ in patterns] == [
        ((0, 1, 1, 1, 1), 8), ((1, 1, 1, 1, 2), 8), ((2, 2, 2, 2, 2), 10)]
    return patterns

def tensor_check():
    level_counts = []
    # Each second-family row uses at least two coordinates in its matching
    # first row, so at most eight outside the first family are ever used.
    m = 18
    expected_cols = sorted(sum(1 << (4*i+j) for i in range(2) for j in range(4)
                               if r in (0,i+1) and s in (0,j+1))
                           for r in range(3) for s in range(5))
    for kind, n, first, pivots in four_pattern_check():
        first_used = (1<<n) - 1
        candidates = [[] for _ in range(4)]
        for coords in combinations(range(m), 4):
            X = sum(1 << j for j in coords)
            if add_basis(X, pivots) is None:
                continue
            old = X & first_used
            negative = old
            while True:
                positive = X ^ negative
                dots = tuple((x & positive).bit_count() - (x & negative).bit_count()
                             for x in first)
                if sorted(dots) == [1,1,1,2]:
                    candidates[dots.index(2)].append((X, positive, negative))
                if not negative:
                    break
                negative = (negative - 1) & old

        counts = [0]*5
        def visit(stack, nxt, pivs):
            i = len(stack)
            counts[i] += 1
            if i == 4:
                signature = sorted(sum(1 << k for k, x in enumerate(
                                       (*first, *(y for y, _, _ in stack)))
                                       if x >> j & 1) for j in range(nxt))
                assert signature == expected_cols and nxt == 15
                # All signs agree on columns occurring in multiple rows.
                allp, alln = first_used, 0
                for _, p, z in stack:
                    allp |= p
                    alln |= z
                assert not (allp & alln)
                return
            for X, pos, neg in candidates[i]:
                # Enumerate modulo permutations of as-yet unseen columns.
                nn = max(nxt, X.bit_length())
                if X >> nxt != (1 << (nn-nxt))-1:
                    continue
                if any((X & Y).bit_count() != 2 or pos & zn or neg & yp
                       for Y, yp, zn in stack):
                    continue
                piv = add_basis(X, pivs)
                if piv is not None:
                    visit((*stack, (X,pos,neg)), nn, piv)
        visit((), n, pivots)
        level_counts.append(tuple(counts))
    assert level_counts == [(1,6,18,18,0), (1,6,18,18,0), (1,28,144,192,64)]
    return level_counts

def tiny_scope_check():
    # Exhaustive integer core-budget check and star classification on 6 vertices.
    for h in range(4,100):
        assert [v for v in range(-2,3) if abs(v)+abs(2-v)+(h-1)*abs(1-v)<=4] == [1]
    edges = [set(x) for x in combinations(range(6),2)]
    count = 0
    for n in (2,3,4,5,6):
        for s in combinations(edges,n):
            if all(x & y for x,y in combinations(s,2)):
                if not set.intersection(*s):
                    assert n == 3 and len(set.union(*s)) == 3
                count += 1
    return count

if __name__ == "__main__":
    print("PASS trace Gram/root representative list rows:", trace_check())
    print("PASS signed rectangular shell cases:", tensor_check())
    print("PASS core budgets / star families:", 96, tiny_scope_check())
