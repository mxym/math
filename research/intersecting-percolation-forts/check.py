"""Direct finite checks for the constructions. All graphs are simple and undirected."""

from collections import deque
from itertools import combinations


def folded_cube(d):
    # Choose the representative whose last bit is zero.
    n = 1 << (d - 1)
    generators = [1 << i for i in range(d - 1)] + [n - 1]
    return [{x ^ a for a in generators} for x in range(n)]


def join_hubs(graph, count):
    n = len(graph)
    hubs = set(range(n, n + count))
    all_vertices = set(range(n + count))
    return [s | hubs for s in graph] + [all_vertices - {h} for h in sorted(hubs)]


def star_times_clique(k, s):
    graph = []
    for layer in range(s + 1):
        for i in range(k):
            neighbors = {layer * k + j for j in range(k) if j != i}
            if layer:
                neighbors.add(i)
            else:
                neighbors.update(layer_id * k + i for layer_id in range(1, s + 1))
            graph.append(neighbors)
    return graph


def percolates(graph, threshold, seeds):
    active = set(seeds)
    queue = deque(active)
    counts = [0] * len(graph)
    while queue:
        for v in graph[queue.popleft()]:
            if v in active:
                continue
            counts[v] += 1
            if counts[v] == threshold:
                active.add(v)
                queue.append(v)
    return len(active) == len(graph)


def verify_minimum(graph, r, witness, translate=False):
    assert percolates(graph, r, witness)
    k = len(witness) - 1
    # By monotonicity it suffices to rule out this one smaller cardinality.
    if translate:
        candidates = ((0,) + other for other in combinations(range(1, len(graph)), k - 1))
    else:
        candidates = combinations(range(len(graph)), k)
    assert all(not percolates(graph, r, s) for s in candidates)


def folded_seeds(d):
    seeds = [0]
    for i in range(0, d - 2, 2):
        vector = 1 << i
        if i + 1 < d - 2:
            vector |= 1 << (i + 1)
        seeds.append(vector)
    return seeds


def minimum_fort(graph, threshold):
    masks = [sum(1 << w for w in neighbors) for neighbors in graph]
    n = len(graph)
    for size in range(1, n + 1):
        for vertices in combinations(range(n), size):
            mask = sum(1 << v for v in vertices)
            if all((masks[v] & ~mask).bit_count() < threshold for v in vertices):
                return size
    raise AssertionError("The full vertex set is always a fort.")


if __name__ == "__main__":
    for d in range(3, 9):
        graph = folded_cube(d)
        seeds = folded_seeds(d)
        assert len(seeds) == (d + 1) // 2
        verify_minimum(graph, 2, seeds, translate=True)
        if d <= 5:
            assert minimum_fort(graph, 2) == 3 * len(graph) // 4
        print(f"folded dimension {d}, minimum seeds {len(seeds)}")
    for d, r in ((6, 3), (7, 3)):
        graph = join_hubs(folded_cube(d), r - 2)
        verify_minimum(graph, r, folded_seeds(d))
        print(f"joined folded dimension {d}, threshold {r}, minimum seeds {(d + 1) // 2}")
    for k, s in ((2, 3), (3, 4), (4, 5)):
        graph = star_times_clique(k, s)
        seeds = [layer * k + (layer == 3) for layer in range(1, s + 1)]
        verify_minimum(graph, 2, seeds)
        print(f"clique order {k}, star leaves {s}, minimum seeds {s}")
