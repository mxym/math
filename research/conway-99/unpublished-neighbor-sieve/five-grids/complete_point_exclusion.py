"""Exact classification for a putative point on 21 grids. Python standard library."""

from collections import Counter
from itertools import combinations, combinations_with_replacement

from complete_point import perfect_matchings


AXES = tuple(range(7))
CELLS = list(combinations(AXES, 2))


def disjoint(a, b):
    return set(CELLS[a]).isdisjoint(CELLS[b])


EDGES = [e for e in combinations(range(21), 2) if disjoint(*e)]
EDGE_INDEX = {e:i for i,e in enumerate(EDGES)}
TRIANGLES = [t for t in combinations(range(21), 3) if all(disjoint(a,b) for a,b in combinations(t,2))]
LOCAL = [list(perfect_matchings([b for b in range(21) if disjoint(a,b)], disjoint))
         for a in range(21)]


def factors_without(axis):
    cells = [a for a in range(21) if axis not in CELLS[a]]
    factors = [t for t in TRIANGLES if all(a in cells for a in t)]
    assert len(cells) == len(factors) == 15
    options = []
    def fill(demand, choice, start):
        if start == len(cells):
            assert sum(choice.values()) == 10 and not any(demand.values())
            masks = [0,0]
            for triangle, weight in choice.items():
                for pair in combinations(triangle,2):
                    masks[weight-1] |= 1 << EDGE_INDEX[pair]
            options.append((choice, *masks))
            return
        a = cells[start]
        possible = [t for t in factors if a in t and all(demand[b] for b in t)]
        for selected in combinations_with_replacement(possible, demand[a]):
            remaining, updated = demand.copy(), choice.copy()
            for t in selected:
                updated[t] = updated.get(t,0)+1
                for b in t:
                    remaining[b] -= 1
            if min(remaining.values()) >= 0:
                fill(remaining, updated, start+1)
    fill(dict.fromkeys(cells,2), {}, 0)
    assert len(options) == len({tuple(sorted(row.items())) for row,_,_ in options}) == 27
    return options


def local_options(a):
    neighbors = sorted(t for t in TRIANGLES if a in t)
    lookup = {}
    for first,second in combinations_with_replacement(range(6),2):
        counts = tuple(sum(tuple(b for b in t if b != a) in LOCAL[a][m] for m in (first,second))
                       for t in neighbors)
        assert counts not in lookup
        lookup[counts] = (first,second)
    return neighbors, lookup


def verify_signed_matrix(matches):
    matrix = [[0]*21 for _ in CELLS]
    full = [set() for _ in CELLS]
    def partners(a,b):
        return tuple(next((d if c == b else c) for c,d in LOCAL[a][i] if b in (c,d))
                     for i in matches[a])
    for a,b in EDGES:
        left, right = partners(a,b), partners(b,a)
        assert sorted(left) == sorted(right)
        if left[0] == left[1]:
            full[a].add(b)
            full[b].add(a)
        else:
            matrix[a][b] = matrix[b][a] = 1 if left == right else -1
    assert all(len(h) == 2 and all((h-{b}) <= full[b] for b in h) for h in full)
    for a,row in enumerate(matrix):
        for b,col in enumerate(matrix):
            assert sum(u*v for u,v in zip(row,col)) == 2*row[b]+8*(a == b)


def main():
    groups = [factors_without(i) for i in AXES]
    local = [local_options(a) for a in range(21)]
    prefixes = Counter()
    survivors = []
    def visit(i, used, doubled, weights):
        prefixes[i] += 1
        if i == 7:
            assert doubled.bit_count() == 105
            matches = []
            for triangles, lookup in local:
                counts = tuple(weights.get(t,0) for t in triangles)
                if counts not in lookup:
                    return
                matches.append(lookup[counts])
            assert all(a != b for a,b in matches)
            verify_signed_matrix(matches)
            survivors.append(tuple(matches))
            return
        for choice, singles, doubles in groups[i]:
            if (singles | doubles) & doubled or doubles & used:
                continue
            visit(i+1, used | singles | doubles, doubled | doubles | (used & singles),
                  weights | choice)
    visit(0,0,0,{})
    assert [prefixes[i] for i in range(8)] == [1,27,198,408,408,408,408,408]
    assert len(survivors) == len(set(survivors)) == 30
    print("408 compatible weighted tables, 30 matching profiles, 30 exact signed-matrix identities.")


if __name__ == '__main__':
    main()
