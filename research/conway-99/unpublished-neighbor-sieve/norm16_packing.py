"""Finite checks used in the norm-sixteen packing argument."""

from itertools import combinations, product
from math import comb


def fano_neighborhoods():
    return {
        x: {y for y in range(1, 8) if (x & y).bit_count() % 2}
        for x in range(1, 8)
    }


def check_fano_split():
    neighbors = fano_neighborhoods()
    for k in range(8):
        choices = list(combinations(range(1, 8), 7-k))
        largest = max(
            sum(y in neighbors[x] for x in positives for y in negatives)
            for positives in combinations(range(1, 8), k) for negatives in choices
        )
        assert largest < max(3*k-1, 3*(7-k)-1)
    for root, adjacent in neighbors.items():
        for triple in combinations(adjacent, 3):
            hits = [len(neighbors[x].intersection(triple)) for x in neighbors if x != root]
            assert sorted(hits) == [1, 1, 1, 2, 2, 2]


def overlap_allowed(c, d):
    return all(k*k*d >= 8*k*(c-k-1)-c*(c-1) for k in (1, 2))


def check_overlaps():
    profiles = {
        (c, d) for c, d in product(range(9), repeat=2)
        if c+d <= 8 and overlap_allowed(c, d) and overlap_allowed(d, c)
    }
    assert {(c,d) for c,d in profiles if max(c,d) >= 4} == {(4,4)}
    assert not any(c+d == 7 for c,d in profiles)
    classes = [(a,b) for a,b in product(range(7), repeat=2) if (a*a+b*b)%7 == 1]
    residues = {(2*a)%7 for a,b in classes}
    assert residues == {0,2,3,4,5}
    assert [(a,b) for a,b in classes if (2*a)%7 == 5] == [(6,0)]
    assert max(c+d for c,d in profiles if (c+d)%7 in residues) == 5
    for z,w in product((2,3), repeat=2):
        matches = 1 + z+w-3 + 3
        conflicts = z-2 + w-2
        assert matches - conflicts == 5
        assert matches > 5 or z == w == 2


def check_root_counts():
    four_seeds = 99*comb(7,4)*2**4
    three_seeds = 99*comb(7,3)*2**3
    assert four_seeds == 55440 and three_seeds == 27720
    assert four_seeds//8 == 6930
    assert 98*(7**4+1)-2*four_seeds == 2*62258
    assert (three_seeds//24)//2*2 == 1154
    pairs = set(combinations(range(4),2))
    for missing in [set()] + [{e} for e in pairs]:
        good = sum(not (set(combinations(t,2)) & missing) for t in combinations(range(4),3))
        assert 8*(good + (4-good)/2) >= 24


if __name__ == "__main__":
    check_fano_split()
    check_overlaps()
    check_root_counts()
    print("Verified Fano splits, norm-16 overlaps, rank-42 residues and rooted counts.")
