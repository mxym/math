"""Two finite matching counts used in the exclusion of a point on 21 grids."""

from collections import Counter
from itertools import combinations, permutations


def perfect_matchings(vertices, adjacent):
    if not vertices:
        yield ()
        return
    first, *rest = vertices
    for second in rest:
        if adjacent(first, second):
            remaining = [v for v in rest if v != second]
            for tail in perfect_matchings(remaining, adjacent):
                yield ((first, second),) + tail


def petersen_count():
    vertices = list(combinations(range(5), 2))
    edges = {edge for edge in combinations(vertices,2) if set(edge[0]).isdisjoint(edge[1])}
    matchings = [set(m) for m in perfect_matchings(vertices, lambda a,b: (a,b) in edges)]
    assert len(edges) == 15 and len(matchings) == 6
    assert all(sum(edge in m for m in matchings) == 2 for edge in edges)
    assert all(len(a & b) == 1 for a,b in combinations(matchings,2))


def square_bijections():
    points = range(4)
    edges = {p for p in combinations(points, 2) if p[0] ^ p[1] in (1,2)}
    for direct in permutations(points):
        aligned = [p for p in edges if tuple(sorted(direct[i] for i in p)) in edges]
        assert len(aligned) in (2,4)
        for pair in aligned:
            a,b = (v for v in points if v not in pair)
            assert (a,b) in aligned
            for indirect in permutations(points):
                if indirect == direct or any(indirect[i] != direct[i] for i in pair):
                    continue
                assert indirect[a] == direct[b] and indirect[b] == direct[a]


def choices_without(axis):
    vertices = [v for v in range(7) if v != axis]
    factors = list(perfect_matchings(vertices, lambda a,b: True))
    assert len(factors) == 15
    for choice in combinations(factors,5):
        covered = {pair for factor in choice for pair in factor}
        if len(covered) == 15:
            yield frozenset(edge for factor in choice for edge in combinations(factor,2))


def seven_factorizations():
    families = [list(choices_without(i)) for i in range(7)]
    assert all(len(options) == 6 and all(len(f) == 15 for f in options) for options in families)
    counts = Counter()
    def visit(i, used):
        counts[i] += 1
        if i < 7:
            for choice in families[i]:
                if used.isdisjoint(choice):
                    visit(i+1, used | choice)
    visit(0, frozenset())
    assert [counts[i] for i in range(8)] == [1,6,0,0,0,0,0,0]
    return [counts[i] for i in range(8)]


if __name__ == "__main__":
    square_bijections()
    petersen_count()
    print("Compatible prefixes of lengths 0 through 7:", seven_factorizations())
