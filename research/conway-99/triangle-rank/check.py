"""Enumerate all triangle shells of Seidel 7-rank at most 30 and check the far-point obstruction."""
from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
from pathlib import Path
import subprocess
import sys

import numpy as np

prior = Path(__file__).resolve().parents[2] / "conway-99-involution" / "seven"
sys.path.insert(0, str(prior))
from check_rank import TWIN, axis_types, eliminate


def canonical(maps):
    """Canonical simultaneous conjugacy key of a list of named permutations."""
    remaining = set(range(12))
    components = []
    while remaining:
        def encode(root):
            order = [root]
            names = {root: 0}
            entries = []
            for point in order:
                for action in maps:
                    image = int(action[point])
                    if image not in names:
                        names[image] = len(order)
                        order.append(image)
                    entries.append(names[image])
            return tuple(entries), order
        _, component = encode(min(remaining))
        components.append(min(encode(i)[0] for i in component))
        remaining.difference_update(component)
    return tuple(sorted(components))


def adjacency(matchings, permutation):
    a = np.zeros((39, 39), dtype=int)
    def edge(i, j):
        a[i,j] = a[j,i] = 1
    for u, v in combinations(range(3), 2):
        edge(u, v)
    for j in range(12):
        for h, matching in enumerate(matchings):
            start = 3+12*h
            edge(h, start+j)
            edge(start+j, start+matching[j])
        edge(3+j, 15+j)
        edge(15+j, 27+j)
        edge(27+j, 3+permutation[j])
    return a


def obstructed(a, reported_rank):
    seidel = 2*a - 1 + np.eye(39, dtype=int)
    operations, pivots, _ = eliminate(seidel)
    rank = len(pivots)
    assert rank == reported_rank and rank in (28, 29, 30)
    kernel = operations[rank:]
    capacity = 2-a-a@a
    pairs, terms, lookup = [], [], []
    for wing in range(3):
        sites = range(3+12*wing, 15+12*wing)
        edges = np.array([(i,j) for i,j in combinations(sites,2) if not a[i,j]])
        assert len(edges) == 60
        pairs.append(edges)
        values = (2*(kernel[:,edges[:,0]] + kernel[:,edges[:,1]]).T) % 7
        terms.append(values)
        index = {}
        for j, value in enumerate(values):
            index.setdefault(tuple(value), []).append(j)
        lookup.append(index)

    bias = kernel.sum(axis=1) % 7
    common_lines = None
    for h in range(3):
        j, k = (h+1)%3, (h+2)%3
        for i, pair in enumerate(pairs[h]):
            target = (bias-terms[h][i]-terms[j]) % 7
            if rank == 28:
                choices = product(range(60), repeat=2)
            else:
                choices = ((b,c) for b in range(60)
                           for c in lookup[k].get(tuple(target[b]), ()))
            has_zero = False
            lines = set()
            for b, c in choices:
                neighbors = tuple(pair)+tuple(pairs[j][b])+tuple(pairs[k][c])
                if any(capacity[u,v] <= 0 for u,v in combinations(neighbors,2)):
                    continue
                if rank == 30:
                    column = np.full(39, -1, dtype=int)
                    column[list(neighbors)] = 1
                    bordered = np.block([[seidel, column[:,None]],
                                         [column[None,:], np.zeros((1,1),dtype=int)]])
                    if len(eliminate(bordered)[1]) > 30:
                        continue
                syndrome = (terms[k][c]-target[b]) % 7
                nonzero = np.flatnonzero(syndrome)
                if not len(nonzero):
                    has_zero = True
                    break
                first_inverse = pow(int(syndrome[nonzero[0]]), -1, 7)
                lines.add(tuple(syndrome*first_inverse % 7))
            if not has_zero:
                common_lines = lines if common_lines is None else common_lines & lines
                if not common_lines:
                    return True
    return False


def main(executable, jobs):
    charts = [(TWIN, p, q) for p, q in axis_types()]
    assert len(charts) == 3580
    rows = [' '.join(str(int(v)) for m in chart for v in m) for chart in charts]
    def run_chunk(start):
        chunk = rows[start:start+128]
        output = subprocess.run([executable], input='\n'.join(chunk)+'\n',
                                text=True, capture_output=True, check=True)
        results = []
        for line in output.stdout.splitlines():
            chart, rank, *permutation = map(int, line.split())
            assert 0 <= chart < len(chunk)
            results.append((start+chart, rank, permutation))
        return results
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(run_chunk, range(0, len(rows), 128)))
    counts = Counter()
    representatives = {}
    for chart, rank, permutation in (row for chunk in results for row in chunk):
        assert sorted(permutation) == list(range(12))
        counts[rank] += 1
        key = (chart, canonical((*charts[chart], permutation)))
        representatives.setdefault(key, (chart,rank,permutation))
    assert counts == {28:8, 29:165, 30:5239} and len(representatives) == 571
    for chart, rank, permutation in representatives.values():
        assert obstructed(adjacency(charts[chart], permutation), rank)
    print(f"{len(charts)} matching charts; shell ranks {dict(sorted(counts.items()))}")
    print(f"{len(representatives)} representative shells; all obstructed at global rank <= 30")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("executable", help="path to the compiled C++ census")
    parser.add_argument("--jobs", type=int, default=1, help="parallel census processes")
    args = parser.parse_args()
    if not __debug__ or args.jobs < 1:
        parser.error("enable Python assertions and use a positive number of jobs")
    main(args.executable, args.jobs)
