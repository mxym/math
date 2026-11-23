"""Rank-38 two-type alternative: rooted overlap count and nine-site census."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product

import pynauty

from enumerate_cores import members, supports


def acceptable(panel, neighbors):
    degrees = {x:len(neighbors[x] & panel) for x in panel}
    if min(degrees.values()) == 0 or sum(d == 1 for d in degrees.values()) > 1:
        return False
    for x,d in degrees.items():
        if d == 1 and any(degrees[y] == 2 for y in neighbors[x] & panel):
            return False
        if d == 4:
            parents = neighbors[x] & panel
            if sum(len(neighbors[y] & parents) == 2 for y in panel-{x}) >= 4:
                return False
    return True


@lru_cache(None)
def common_type(positive_rows):
    p = len(positive_rows)
    neighbors = {i:[] for i in range(9)}
    for i,row in enumerate(positive_rows):
        for j in members(row):
            neighbors[i].append(p+j)
            neighbors[p+j].append(i)
    colors = [{0},set(range(1,p)),set(range(p,p+4)),set(range(p+4,9))]
    graph = pynauty.Graph(9, adjacency_dict=neighbors, vertex_coloring=[s for s in colors if s])
    return pynauty.certificate(graph)


def nine_site_types(graph):
    neighbors = [set(members(row)) for row in graph]
    sites = set(range(18))
    result = set()
    for root in sites:
        positives = set(range(9)) if root < 9 else set(range(9,18))
        parents = neighbors[root]
        labels = {x for x in positives-{root} if len(neighbors[x] & parents) == 2}
        for p in range(3,6):
            for marked in combinations(sorted(positives-{root}),p-1):
                count = len(labels.intersection(marked))
                if count not in (2,3):
                    continue
                for extra in combinations(sorted(sites-positives-parents),5-p):
                    panel = {root,*parents,*marked,*extra}
                    if not acceptable(panel,neighbors) or not acceptable(sites-panel,neighbors):
                        continue
                    columns = sorted(parents) + list(extra)
                    rows = tuple(sorted(sum(1<<j for j,v in enumerate(columns) if v in neighbors[x])
                                        for x in marked))
                    result.add((p,count,common_type((15,*rows))))
    return result


def exceptional_pair_profiles():
    # In the panel with eleven internal edges, the unique first-color pair
    # missing a common neighbor contains its distinguished triangle vertex.
    rows = (15,19,60)
    pairs = [(i,j) for i,j in combinations(range(3),2) if (rows[i] & rows[j]).bit_count() == 1]
    assert pairs == [(1,2)]
    assert [v.bit_count() for v in rows] == [4,3,4]
    a,b = (rows[i] for i in pairs[0])
    assert ((a & ~b).bit_count(),(b & ~a).bit_count()) == (2,3)
    profiles = set()
    for first in product(range(3), repeat=3):
        if first[0] != 2 or first.count(2) > 1:
            continue
        for balance in range(-6,3):
            second = tuple(v-balance for v in first)
            if min(second) < 0 or any(first[i]+second[j] > 2 for i,j in combinations(range(3),2)):
                continue
            profiles.add((first,second))
    assert profiles == {((2,0,0),(2,0,0)), ((2,1,1),(1,0,0))}
    assert 2*3 + (2+3)*2*2 == 26


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--genbg', default='genbg')
    args = parser.parse_args()
    exceptional_pair_profiles()
    one_support = supports(args.genbg)
    assert len(one_support) == 26
    shapes = set().union(*(nine_site_types(g) for g in one_support))
    counts = Counter((p,d) for p,d,_ in shapes)
    assert counts == {(3,2):2,(4,2):11,(4,3):8,(5,3):3}
    print('Rooted common panels by positives and shared pair labels:',dict(sorted(counts.items())))


if __name__ == '__main__':
    main()
