"""Unconditional count of uncovered squares forced by a point on fifteen grids."""

from collections import Counter
from itertools import combinations, combinations_with_replacement

from complete_point import perfect_matchings
from complete_point_exclusion import CELLS, disjoint


DIRTY = {CELLS.index((i,j)) for i in (0,1) for j in (2,3,4)}
REGULAR = [a for a,c in enumerate(CELLS) if c == (0,1)
           or (c[0] in (0,1) and c[1] in (5,6))
           or (c[0] in (2,3,4) and c[1] in (2,3,4))]


def pair_test(a,b):
    if not disjoint(a,b) or a in DIRTY or b in DIRTY:
        return 0
    dirty_thirds = sum(disjoint(a,c) and disjoint(b,c) for c in DIRTY)
    if dirty_thirds and not (a in REGULAR and b in REGULAR):
        return 0
    return 2 if dirty_thirds <= 1 else 1  # both imply evenness; 2 also tests coverage


def candidate_rows(a):
    def can_pair(b,c):
        return disjoint(b,c) or (b in DIRTY and c in DIRTY)
    cells = [b for b in range(21) if disjoint(a,b)]
    matchings = [set(tuple(sorted((a,b,c))) for b,c in pairs)
                 for pairs in perfect_matchings(cells, can_pair)]
    triples = sorted(set.union(*matchings))
    needs_even = [any(pair_test(b,c) for b,c in combinations(t,2)) for t in triples]
    rows = set()
    for four in combinations_with_replacement(matchings,4):
        counts = tuple(sum(t in m for m in four) for t in triples)
        if all(not parity or n % 2 == 0 for parity,n in zip(needs_even,counts)):
            rows.add(counts)
    return triples, sorted(rows)


def main():
    data = {a:candidate_rows(a) for a in REGULAR}
    projections = {}
    for a,b in combinations(REGULAR,2):
        shared = sorted(t for t in set(data[a][0]) | set(data[b][0]) if a in t and b in t)
        for i,j in ((a,b),(b,a)):
            triples,rows = data[i]
            positions = [triples.index(t) if t in triples else None for t in shared]
            projections[i,j] = [tuple(0 if k is None else row[k] for k in positions) for row in rows]
    counts = Counter()
    def visit(options, chosen):
        if not options:
            uncovered = set()
            for a, idx in chosen.items():
                triples,rows = data[a]
                for t,n in zip(triples, rows[idx]):
                    if n == 2:
                        uncovered.update(pair for pair in combinations(t,2) if pair_test(*pair) == 2)
            counts[len(uncovered)] += 1
            return
        a = min(options, key=lambda i:len(options[i]))
        for j in options[a]:
            remaining = {b:[k for k in inds if projections[a,b][j] == projections[b,a][k]]
                         for b,inds in options.items() if b != a}
            if all(remaining.values()):
                visit(remaining, chosen | {a:j})
    visit({a:list(range(len(data[a][1]))) for a in REGULAR}, {})
    assert counts == {18:6,22:30,23:12,24:12,25:12,26:12,28:6}
    print("90 profiles. Counts by number of cell pairs forcing uncovered squares:", dict(sorted(counts.items())))


if __name__ == '__main__':
    main()
