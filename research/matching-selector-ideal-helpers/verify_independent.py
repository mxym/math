#!/usr/bin/env python3
"""Independent finite-field rank tests and exact cost-accounting checks."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from random import Random


def rank(rows, p):
    basis = {}
    for raw in rows:
        row = list(raw)
        for j, r in sorted(basis.items()):
            if row[j]:
                a = row[j]
                row = [(x-a*y) % p for x, y in zip(row, r)]
        j = next((j for j, x in enumerate(row) if x), None)
        if j is not None:
            a = pow(row[j], -1, p)
            basis[j] = [a*x % p for x in row]
    return len(basis)


def spancheck(m, matchings, p, width, extras):
    r = len(matchings)
    n = 2*m+r
    v = [list() for _ in range(n)]
    dims = width*(1+m*r)+sum(extras)

    def unit(i):
        return tuple(1 if j == i else 0 for j in range(dims))

    sec = [unit(i) for i in range(width)]
    ix = width
    for s, mate in enumerate(matchings):
        for j, Sj in enumerate(sec):
            pad_ids = []
            for i, k in enumerate(mate):
                v[i].append(unit(ix))
                v[m+k].append(unit(ix))
                pad_ids.append(ix)
                ix += 1
            v[2*m+s].append(tuple((x-int(i in pad_ids)) % p for i, x in enumerate(Sj)))
    for s, e in enumerate(extras):
        for z in range(e):
            v[2*m+s].append(unit(ix))
            ix += 1

    def subset_rows(C):
        return [row for i in C for row in v[i]]

    coalitions = 0
    for J in range(n+1):
        for C in combinations(range(n), J):
            cover = False
            for s, mate in enumerate(matchings):
                if 2*m+s in C and not any(
                        i not in C and m+mate[i] not in C for i in range(m)):
                    cover = True
            rows = subset_rows(C)
            increment = rank(rows+sec, p)-rank(rows, p)
            assert increment == (0 if cover else width)
            coalitions += 1

    for side in [tuple(range(m)), tuple(range(m, 2*m))]:
        full = subset_rows(side)
        assert rank(full, p) == m*r*width
        for i in side:
            others = subset_rows(tuple(j for j in side if j != i))
            assert rank(full, p)-rank(others, p) == r*width
            assert rank(full+sec, p)-rank(others+sec, p) == r*width
    for s, e in enumerate(extras):
        assert rank(v[2*m+s], p) == width+e
    return coalitions


latin = [(0,1,2,3),(1,0,3,2),(2,3,0,1),(3,2,1,0)]
cyc3 = [(0,1,2),(1,2,0),(2,0,1)]
cases = [(1,[(0,)],2,2,[0]), (2,[(0,1),(1,0)],3,2,[0,1]),
         (3,cyc3,2,1,[0,0,0]), (3,cyc3[:2],5,2,[2,0]),
         (4,latin,2,1,[0,0,0,0])]
views = sum(spancheck(*x) for x in cases)

# Enumerate admissibility of the two-erasure witnesses for every matching
# packing of size one through three on 4+4 positions, with no cyclic assumption.
perms = list(permutations(range(4)))
packings = cuts = 0
for r in range(1, 4):
    for M in combinations(perms, r):
        if any(len({a[i] for a in M}) != r for i in range(4)):
            continue
        packings += 1
        for i, s in product(range(4), range(r)):
            v = M[s][i]
            for t in range(r):
                lacking = {j for j, x in enumerate(M[t]) if j == i and x == v}
                assert bool(lacking) == (t == s)
                cuts += 1

# Independent exhaustive ordered-subset optimization over asymmetric defects.
rng = Random(20725)
frontiers = 0
strict = 0
for r in range(1, 7):
    trials = [[F(0)]*r] + [[F(rng.randrange(0, 13), 12)
                             for _ in range(r)] for _ in range(13)]
    for es in trials:
        target = max(F(0), F(r)-F(r+1, 2)*sum(es))
        exact = max(F(j)-sum(F(j-u)*es[i] for u, i in enumerate(J))
                    for j in range(r+1) for J in permutations(range(r), j))
        sorted_es = sorted(es)
        thresholds = F(0)
        accum = F(0)
        for e in sorted_es:
            accum += e
            thresholds += max(F(0), 1-accum)
        assert exact == thresholds >= target
        strict += exact > target
        frontiers += 1
assert strict > 0
print(f"independent PASS: {len(cases)} field models, {views} full rank views; "
      f"{packings} distinct matching packings, {cuts} two-erasure witnesses")
print(f"independent PASS: {frontiers} ordered-subset defect optimizations "
      f"({strict} strict refinements)")
