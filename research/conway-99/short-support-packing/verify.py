"""Check generation from Fano triples and the rank-34 integer bounds."""
from itertools import combinations
from math import comb


def check_fano():
    points = set(range(1, 8))
    incident = {i: {j for j in points if (i & j).bit_count() % 2} for i in points}
    for seed in combinations(points, 3):
        left, right = set(seed), set()
        while True:
            a = left | {i for i in points if len(incident[i] & right) >= 2}
            b = right | {i for i in points if len(incident[i] & left) >= 2}
            if (a, b) == (left, right):
                break
            left, right = a, b
        assert left == right == points
    assert 99 * comb(7, 3) * 8 == 990 * 7 * comb(4, 3)


def minimum_at_prism_count(p):
    pairs, grids = 5*p//2, p//6
    y3 = 24948 + max(0, 7392-2*p-4*pairs) + 2*(20790-9*p-36*grids)
    y4 = 1398474 + 765072+18*p-48*pairs + 2*(831600+36*p-2286*grids)
    required = -13804112 + 2737*462 + 196*y3 + 7*y4
    max_weight = 0
    for n14 in range(0, 991, 2):
        cap = min((55440-7*n14)//4, (77616+24*p-14*n14)//8)
        n16 = 2*(cap//2)
        max_weight = max(max_weight, 2387*n14 + 407*n16)
    return 2*((required-max_weight+85)//86)


if __name__ == "__main__":
    check_fano()
    bounds = [minimum_at_prism_count(p) for p in range(852)]
    assert min(bounds) == bounds[-1] == 254844 and bounds[0] == 537904
    print("35 Fano closures verified; N18 >= 254844, and >= 537904 if prism-free")
