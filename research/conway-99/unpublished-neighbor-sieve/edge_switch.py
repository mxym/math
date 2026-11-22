"""Enumerate the signed twenty-site supports with an edge; pynauty is used for isomorphism."""

from collections import Counter
from itertools import combinations
from math import comb

import pynauty


def cross_matrices(matches):
    # The first two vertices on each side are the endpoints of its internal edge.
    # A type is the bit mask of neighbors among the opposite two endpoints.
    types = [1, 2 if matches == 2 else 0, 3]
    for mask, total in ((1, 4), (2, 4), (0, 1)):
        types.extend([mask] * (total - types[:2].count(mask)))
    assert len(types) == 10
    rows = [sum(((mask >> j) & 1) << i for i, mask in enumerate(types)) for j in (0, 1)]
    columns = types.copy()
    choices = [[m for m in range(1024) if m.bit_count() == 4 and m & 3 == mask]
               for mask in types]
    target = [5, 5] + [4]*8

    def complete(i):
        if i == 10:
            yield tuple(rows)
            return
        for m in choices[i]:
            if i > 2 and types[i] == types[i-1] and m < rows[-1]:
                continue
            if any((r & m).bit_count() > 2 for r in rows):
                continue
            if any(types[j] == types[j-1] and columns[j] == columns[j-1]
                   and (m >> (j-1)) & 3 == 2 for j in range(3,10)):
                continue
            chosen = [j for j in range(10) if m & (1 << j)]
            if any((columns[a] & columns[b]).bit_count() >= 2-(a == 0 and b == 1)
                   for a,b in combinations(chosen, 2)):
                continue
            degrees = [c.bit_count() + ((m >> j) & 1) for j,c in enumerate(columns)]
            if any(not (n <= goal <= n + 9-i) for n,goal in zip(degrees,target)):
                continue
            rows.append(m)
            for j in chosen:
                columns[j] |= 1 << i
            yield from complete(i+1)
            for j in chosen:
                columns[j] ^= 1 << i
            rows.pop()

    yield from complete(2)


def signed_graph(rows):
    graph = [set() for _ in range(20)]
    graph[0].add(1)
    graph[1].add(0)
    graph[10].add(11)
    graph[11].add(10)
    for i,row in enumerate(rows):
        for j in range(10):
            if row & (1 << j):
                graph[i].add(j+10)
                graph[j+10].add(i)
    return graph


def census():
    seen = set()
    counts = Counter()
    raw = Counter()
    unoriented = {}
    for matches in (1, 2):
        for rows in cross_matrices(matches):
            raw[matches] += 1
            adjacency = signed_graph(rows)
            assert all(len(adjacency[i] & adjacency[j]) <= 2-int(j in adjacency[i])
                       for i,j in combinations(range(20),2))
            graph = pynauty.Graph(20, adjacency_dict=dict(enumerate(adjacency)),
                                  vertex_coloring=[set(range(10)),set(range(10,20))])
            certificate = pynauty.certificate(graph)
            if certificate in seen:
                continue
            seen.add(certificate)
            # The third vertex on each of the two triangles has index 2 on its side.
            category = matches, 12 in adjacency[2]
            counts[category] += 1
            reverse = pynauty.Graph(20, adjacency_dict=dict(enumerate(adjacency)),
                                    vertex_coloring=[set(range(10,20)),set(range(10))])
            pair = min(certificate, pynauty.certificate(reverse))
            unoriented.setdefault(category,set()).add(pair)
    assert raw == {1:168, 2:242}
    assert counts == {(1,False):40, (1,True):48, (2,False):71, (2,True):23}
    paired_counts = {k:len(v) for k,v in unoriented.items()}
    assert paired_counts == {(1,False):30, (1,True):32, (2,False):50, (2,True):20}
    return counts, paired_counts


def verify_counts():
    # Pairs of the four endpoints of the two positive F1 edges.
    assert 2*comb(4,2)-2 == 10
    assert 4*7-18 == 10
    # Triangle translation and the two squared norms for the edge translation.
    assert 39+24-14*2 == 35 and 39+35-12*3-14 == 24
    assert 36+28-2*(14+4*2) == 20 and 36+20-2*14 == 28


if __name__ == "__main__":
    verify_counts()
    oriented, paired = census()
    print("Signed shapes:", oriented)
    print("Shapes up to sign reversal:", paired)
