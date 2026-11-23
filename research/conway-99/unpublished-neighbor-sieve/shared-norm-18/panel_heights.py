"""Verify the rank-38 two-type panel sieve using integer arithmetic."""

import argparse
from collections import Counter
from functools import lru_cache
import gzip
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from math import comb
from pathlib import Path

import numpy as np

from enumerate_cores import add_edge, mask, members, supports, valid
from forced_pair import common_type, nine_site_types


ROOTED = [
    (15,19,60), (15,51,60),
    (15,1,19,28), (15,3,5,25), (15,3,5,26), (15,3,12,21),
    (15,3,17,21), (15,3,17,22), (15,3,17,28), (15,3,20,21),
    (15,3,20,25), (15,3,20,28), (15,3,21,22), (15,3,21,26),
    (15,3,21,28), (15,16,19,28), (15,17,19,22), (15,17,19,28),
    (15,17,22,26), (15,19,21,22), (15,19,21,26),
    (15,1,3,5,10), (15,1,3,6,10), (15,1,3,6,12),
]
PREVIOUS_EXCLUSIONS = {(15,51,60), (15,19,21,22)}
PAIRS = list(combinations_with_replacement(range(6), 2))


def panel(rows):
    size = len(rows)
    graph = [0] * 9
    for i, row in enumerate(rows):
        for j in members(row):
            add_edge(graph, i, size+j)
    return graph


def root_test(graph, size):
    for i, neighbors in enumerate(graph):
        if neighbors.bit_count() != 4:
            continue
        side = range(size) if i < size else range(size, 9)
        counts = [(graph[j] & neighbors).bit_count() for j in side if j != i]
        if not 2 + 2*counts.count(0) <= counts.count(2) <= 3:
            return False
    return True


def degrees(graph):
    return tuple(tuple(sorted(v.bit_count() for v in side)) for side in (graph[:4], graph[4:]))


PERMUTED = [[mask(perm[j] for j in members(row)) for row in range(32)]
            for perm in permutations(range(5))]


def canonical_rows(rows):
    return min(tuple(sorted(table[row] for row in rows)) for table in PERMUTED)


def small_side_rows(rows):
    if len(rows) == 5:
        rows = [mask(i for i, row in enumerate(rows) if row >> j & 1) for j in range(4)]
    assert len(rows) == 4
    return canonical_rows(rows)


def four_by_five_panels():
    panels = {}
    for rows in combinations_with_replacement(range(1, 31), 4):
        if sum(row.bit_count() for row in rows) not in (11, 12, 13):
            continue
        graph = panel(rows)
        ds = [v.bit_count() for v in graph]
        if min(ds) < 1 or ds.count(1) > 1 or not valid(graph) or not root_test(graph, 4):
            continue
        if any(ds[j] == 2 for i, d in enumerate(ds) if d == 1 for j in members(graph[i])):
            continue
        key = canonical_rows(rows)
        if rows == key:
            panels[key] = graph
    return panels


def coarse_target(profiles):
    sides = [side for profile in profiles for side in profile]
    sizes = list(map(len, sides))
    edges = sum(sides[0])
    target = [72] + [6*n + edges for n in sizes]
    for i, j in PAIRS:
        a, b = i//2, j//2
        if i == j:
            missing = sizes[i]*(sizes[i]-1) - sum(comb(d, 2) for d in sides[i^1])
            missing -= sum(comb(4-d, 2) for k in range(i%2, 6, 2) if k != i for d in sides[k])
        elif a == b:
            missing = 2*sizes[i]*sizes[j] - edges
        elif i%2 == j%2:
            third = 2*(3-a-b) + i%2
            missing = 2*sizes[i]*sizes[j] - (4*sizes[i]-edges) - sum((4-d)**2 for d in sides[third])
        else:
            missing = 2*sizes[i]*sizes[j] - sum(d*(4-d) for k in (i^1, j^1) for d in sides[k])
        target.append(missing)
    return target


@lru_cache(None)
def coarse_system(profiles):
    leaves = [sum(side.count(1) for side in profile) for profile in profiles]
    patterns, columns = [], []
    for counts in product(product(range(4), repeat=2), repeat=3):
        if len({u-v for u, v in counts}) != 1:
            continue
        heights = tuple(counts[(j+1)%3][0] + counts[(j+2)%3][1] for j in range(3))
        if any(h > 3-leaf for h, leaf in zip(heights, leaves)):
            continue
        flat = sum(counts, ())
        moments = [comb(flat[i], 2) if i == j else flat[i]*flat[j] for i, j in PAIRS]
        columns.append([1, *flat, *moments, *(int(h == 3) for h in heights)])
        patterns.append((counts[0], heights))
    target = coarse_target(profiles) + [1-leaf for leaf in leaves]
    return np.asarray(columns, dtype=int).T, target, patterns


def add_slacks(rows, indices):
    return np.column_stack((rows, np.eye(len(rows), dtype=int)[:, indices]))


def detailed_system(graph, profiles):
    coarse, target, patterns = coarse_system(profiles)
    target = target.copy()
    ds = [r.bit_count() for r in graph]
    quotas = {(i,j): 2-(graph[i] >> j & 1)-(graph[i]&graph[j]).bit_count()
              for i,j in combinations(range(9), 2)}
    allowed = {}
    for word in range(512):
        if any((word & (r | (1 << i))).bit_count() > 2 for i,r in enumerate(graph)):
            continue
        if any(not quotas[pair] for pair in combinations(members(word), 2)):
            continue
        counts = (word & 15).bit_count(), (word >> 4).bit_count()
        allowed.setdefault(counts, []).append(word)

    exterior = []
    for k, (counts, heights) in enumerate(patterns):
        for word in allowed.get(counts, ()):
            if any((heights[0] >= 2 and ds[i] == 1) or (heights[0] == 3 and ds[i] <= 2)
                   for i in members(word)):
                continue
            exterior.append((word, k, heights))

    # A site in a companion panel has 4-d contacts of its own color here.
    companion = []
    groups = [(j,c,d) for j in (1,2) for c in range(2) for d in sorted(set(profiles[j][c]))]
    for j, color, d in groups:
        for subset in combinations(range(4,9) if color else range(4), 4-d):
            word = mask(subset)
            if all(quotas[pair] for pair in combinations(subset, 2)) and all(
                    (r & word).bit_count() <= 2 for r in graph):
                companion.append((j, color, d, word))

    bits = np.array([[w >> i & 1 for w, k, h in exterior] for i in range(9)])
    cross = np.array([[w >> i & 1 for j, c, d, w in companion] for i in range(9)])
    heights = np.array([h for w, k, h in exterior]).T
    rows = list(np.column_stack((coarse[:, [k for w,k,h in exterior]],
                                 np.zeros((len(target), len(companion)), dtype=int))))
    slack = list(range(len(target)-3, len(target)))
    ext_zero = np.zeros(len(exterior), dtype=int)
    cross_zero = np.zeros(len(companion), dtype=int)

    def append(total, ext, other):
        rows.append(np.r_[ext, other])
        target.append(total)

    for j, c, d in groups:
        append(profiles[j][c].count(d), ext_zero,
               [int((j,c,d) == entry[:3]) for entry in companion])
    for i, d in enumerate(ds):
        append(6+d, bits[i], cross_zero)
        append(d-2 + sum(ds[z] for z in members(graph[i])), bits[i]*heights[0], cross_zero)
        for j in (1,2):
            incident = cross[i]*np.array([int(k == j) for k,c,dz,w in companion])
            append(4-d, ext_zero, incident)
            append(14, bits[i]*heights[j], incident*np.array([4-dz for k,c,dz,w in companion]))
    for (i,j), quota in quotas.items():
        append(quota, bits[i]*bits[j], cross[i]*cross[j])
    return add_slacks(rows, slack), target


def check_certificate(matrix, target, sparse):
    # Use Python integers for both the target and every column.
    seen = set()
    combined = np.zeros(matrix.shape[1], dtype=object)
    score = 0
    for i, weight in sparse:
        assert type(i) is int and 0 <= i < len(target) and i not in seen
        assert type(weight) is int and weight
        seen.add(i)
        combined += weight * matrix[i].astype(object)
        score += weight * int(target[i])
    assert score < 0 and min(combined) >= 0


def check_height_counts():
    possibilities = []
    for m in range(7):
        zeros, ones, twos = 9-m, 54+3*m, 18-3*m
        assert zeros+ones+twos+m == 81 and ones+2*twos+3*m == 90
        assert twos+3*m == 18
        if m < 2 or 2*5-zeros <= 2:
            possibilities.append((zeros, ones, twos, m))
    assert possibilities == [(9,54,18,0), (8,57,15,1)]
    triple_neighbors = [(8-a-b,a,b) for a in range(9) for b in range(2) if a+2*b == 3]
    assert triple_neighbors == [(6,1,1), (5,3,0)]
    assert 6+4-8 > 1
    assert [(c,d) for c in range(10) for d in range(10)
            if 12*(18-2*c) == 9*(18-2*d)] == [(3,1),(6,5),(9,9)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--genbg', default='genbg')
    args = parser.parse_args()
    check_height_counts()
    actual = set().union(*(nine_site_types(g) for g in supports(args.genbg)))
    catalog = {(len(r), sum((w & 15).bit_count() == 2 for w in r[1:]), common_type(r))
               for r in ROOTED}
    assert actual == catalog and len(catalog) == len(ROOTED) == 24
    rerooted = {r for r in ROOTED if not root_test(panel(r), len(r))}
    assert rerooted == {(15,19,60), (15,16,19,28)}

    panels = four_by_five_panels()
    assert len(panels) == 28
    profiles = {r: degrees(g) for r, g in panels.items()}
    eleven = sorted({p for p in profiles.values() if sum(p[0]) == 11})
    leaves = {r for r,p in profiles.items() if sum(p[0]) == 11 and any(1 in side for side in p)}
    assert len(eleven) == 7 and len(leaves) == 12
    required = {(r,b,c) for r in leaves for b,c in combinations_with_replacement(eleven,2)}
    counts = Counter()
    with gzip.open(Path(__file__).with_name('panel-height-duals.json.gz'), 'rt') as stream:
        for rows, b, c, method, sparse in json.load(stream):
            r = tuple(rows)
            ps = profiles[r], tuple(map(tuple,b)), tuple(map(tuple,c))
            required.remove((r,ps[1],ps[2]))
            if method == 'coarse':
                base, target, _ = coarse_system(ps)
                matrix = add_slacks(base, list(range(len(target)-3, len(target))))
            else:
                assert method == 'face'
                matrix, target = detailed_system(panels[r], ps)
            check_certificate(matrix, target, sparse)
            counts[method] += 1
    assert not required and counts == {'coarse':295, 'face':41}
    remaining = [r for r in ROOTED if r not in PREVIOUS_EXCLUSIONS | rerooted]
    assert all(len(r) in (4,5) and sum(w.bit_count() for w in r) in (11,12,13)
               for r in remaining)
    remaining = [r for r in remaining if small_side_rows(r) not in leaves]
    assert len(remaining) == 10 and all(len(r) == 4 for r in remaining)
    print('All 336 integer separators verified. Rooted panels before the three-label core check, by edge count:',
          dict(sorted(Counter(sum(w.bit_count() for w in r) for r in remaining).items())))
    for rows in remaining:
        print(rows)


if __name__ == '__main__':
    main()
