"""Rebuild the archived core catalogue using nauty genbg and pynauty."""

import argparse
from collections import defaultdict
import gzip
from itertools import combinations, permutations, product
import json
from pathlib import Path
import subprocess

import pynauty


LABEL_SETS = (((0, 1), (0, 2), (0, 3), (1, 2)),
              ((0, 1), (0, 2), (1, 3), (2, 3)))
COMMON = (1 << 9) - 1
COLORS = [set(range(start, start + n)) for start, n in
          ((0, 5), (5, 4), (9, 5), (14, 4), (18, 5), (23, 4))]


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def mask(indices):
    return sum(1 << i for i in indices)


def add_edge(graph, i, j):
    graph[i] |= 1 << j
    graph[j] |= 1 << i


def valid(graph):
    return all((a & graph[j]).bit_count() <= 2 - ((a >> j) & 1)
               for i, a in enumerate(graph) for j in range(i))


def supports(genbg):
    records = subprocess.check_output([genbg, '-q', '-d4', '-D4', '-Z2', '9', '9']).splitlines()
    assert len(records) == 68
    out = []
    for record in records:
        assert record[0] - 63 == 18
        bits = ((byte - 63) >> i & 1 for byte in record[1:] for i in range(5, -1, -1))
        graph = [0] * 18
        for j in range(18):
            for i in range(j):
                if next(bits):
                    add_edge(graph, i, j)
        if valid(graph):
            out.append(graph)
    assert len(out) == 26
    return out


def orders(vertices, base, graph):
    groups = defaultdict(list)
    for v in vertices:
        groups[mask(i for i, b in enumerate(base) if graph[v] >> b & 1)].append(v)
    keys = sorted(groups)
    masks = tuple(k for k in keys for _ in groups[k])
    orderings = [sum(parts, ()) for parts in product(*(permutations(groups[k]) for k in keys))]
    return masks, orderings


def charts(graphs, labels):
    seen = set()
    for graph in graphs:
        for root, neighbors in enumerate(graph):
            pos = set(range(0, 9) if root < 9 else range(9, 18))
            neg = set(range(18)) - pos
            for parents in permutations(members(neighbors)):
                other = [(graph[parents[i]] & graph[parents[j]]) & ~(1 << root) for i, j in labels]
                if not all(other):
                    continue
                assert all(x.bit_count() == 1 for x in other) and len(set(other)) == 4
                marked = [root, *(x.bit_length() - 1 for x in other)]
                a, rows = orders(neg - set(parents), marked, graph)
                b, cols = orders(pos - set(marked), parents, graph)
                matrix = min(tuple(mask(j for j, v in enumerate(col) if graph[u] >> v & 1)
                                   for u in row) for row, col in product(rows, cols))
                seen.add((a, b, matrix))
    result = []
    for a, b, matrix in sorted(seen):
        graph = [0] * 18
        for i, positions in enumerate((range(4), *labels)):
            for j in positions:
                add_edge(graph, i, 5 + j)
        for start, target, rows in [(9, 0, a), (14, 5, b), (9, 14, matrix)]:
            for i, row in enumerate(rows):
                for j in members(row):
                    add_edge(graph, start + i, target + j)
        result.append(graph)
    return result


def place(graph, start, rows):
    result = graph.copy()
    for i, row in enumerate(rows):
        for j in members(row):
            add_edge(result, start + i, start + 9 + j)
    return result


def crossing_matrices(graph, start, n):
    first = graph[start:start+n]
    second = graph[start+9:start+9+n]
    columns = [(v & COMMON).bit_count() for v in second]
    choices = [[mask(js) for js in combinations(range(n), (v & COMMON).bit_count())
                if all((v & second[j]).bit_count() <= 1 for j in js)] for v in first]

    def extend(rows):
        i = len(rows)
        if i == n:
            yield rows
            return
        full = mask(j for j, c in enumerate(columns) if c == n-i)
        empty = mask(j for j, c in enumerate(columns) if not c)
        for row in choices[i]:
            if row & empty or (row & full) != full:
                continue
            sites = list(members(row))
            for j in sites:
                columns[j] -= 1
            yield from extend(rows + (row,))
            for j in sites:
                columns[j] += 1
    return extend(())


def gluings(wings, first_sign=5):
    for i, first in enumerate(wings):
        for second in wings[i:]:
            graph = [first[k] | ((second[k] & ~COMMON) << 9) for k in range(9)]
            graph += first[9:] + [(v & COMMON) | ((v & ~COMMON) << 9) for v in second[9:]]
            if not valid(graph):
                continue
            for plus in crossing_matrices(graph, 9, first_sign):
                partial = place(graph, 9, plus)
                if valid(partial):
                    for minus in crossing_matrices(partial, 9+first_sign, 9-first_sign):
                        full = place(partial, 9+first_sign, minus)
                        if valid(full):
                            yield full


def certificate(graph):
    neighbors = {i: list(members(v)) for i, v in enumerate(graph)}
    return pynauty.certificate(pynauty.Graph(27, adjacency_dict=neighbors, vertex_coloring=COLORS))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--genbg', default='genbg', help='path to the nauty genbg executable')
    args = parser.parse_args()
    graphs = supports(args.genbg)
    with gzip.open(Path(__file__).with_name('cores.json.gz'), 'rt') as f:
        archive = json.load(f)
    for i, labels in enumerate(LABEL_SETS):
        wings = charts(graphs, labels)
        seen = set()
        total = 0
        for graph in gluings(wings):
            total += 1
            seen.add(certificate(graph))
        assert len(seen) == len(archive[i]) and seen == set(map(certificate, archive[i]))
        print(i, len(wings), total, len(seen), flush=True)


if __name__ == '__main__':
    main()
