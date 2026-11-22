"""Exact counting certificate for the proportion of admissible uncovered squares."""

from itertools import combinations, product

# Bits are given in cyclic order, starting at the root.
SCORE = {0: 10, 1: 1, 2: 3, 3: -3, 4: 10, 5: 1, 6: 3,
         7: 0, 10: -1, 11: 0, 14: 0}
# A diagonal precludes all flips. Two disjoint flips leave no uncovered label.
CELL_EDGES = [(), ((0, 3),), ((0, 3), (1, 2)), ((0, 1),), ((0, 1), (0, 2))]


def score(mark_mask, four_caps=False):
    reflection = (mark_mask & 5) | ((mark_mask & 2) << 2) | ((mark_mask & 8) >> 2)
    return 0 if four_caps else SCORE[min(mark_mask, reflection)]


def parents(label):
    return {label & 1, 2 + (label >> 1)}


def partitions(items):
    """Set partitions of up to four remaining contacts for one signed parent."""
    if not items:
        yield ()
        return
    first, *rest = items
    for blocks in partitions(rest):
        yield (frozenset({first}), *blocks)
        for i, block in enumerate(blocks):
            yield (*blocks[:i], block | {first}, *blocks[i + 1:])


def options(label, adjacency, blocks):
    """Rooted scores allowed by the two partners on the square edges opposite the root."""
    a, b = sorted(parents(label))
    u = next(block for block in blocks[a] if label in block)
    v = next(block for block in blocks[b] if label in block)
    opposite = label ^ 3
    root_mark = opposite in adjacency[label]
    a_mark = (label ^ 1) in u
    b_mark = (label ^ 2) in v
    if a_mark and b_mark and {label ^ 1, label ^ 2} <= adjacency[opposite]:
        return []  # Forbidden eleven-vertex subgraph.
    triple_a, triple_b = opposite in u, opposite in v
    if (triple_a and (root_mark or a_mark)) or (triple_b and (root_mark or b_mark)):
        return []  # The associated incident cap pair already has two common neighbors.
    if triple_a and triple_b:
        return [score(0, four_caps=True)]
    mask = int(root_mark) + 2 * a_mark + 8 * b_mark
    return [score(mask + 4 * other) for other in (0, 1) if mask + 4 * other != 15]


def check_cell(edges):
    adjacency = [set() for _ in range(4)]
    for i, j in edges:
        adjacency[i].add(j)
        adjacency[j].add(i)
    uncovered = [i for i in range(4) if not adjacency[i] & {i ^ 1, i ^ 2}]
    choices = []
    for p in range(4):
        own = {i for i in range(4) if p in parents(i)}
        missing = [i for i in range(4) if not adjacency[i] & own]
        choices.append([parts for parts in partitions(missing)
                        if all(len(block & own) <= 1 for block in parts)])
    available = {(i, j): 2 - int(j in adjacency[i]) - len(parents(i) & parents(j))
                 - len(adjacency[i] & adjacency[j]) for i, j in combinations(range(4), 2)}
    count = 0
    minimum = None
    for blocks in product(*choices):
        if any(sum(i in block and j in block for group in blocks for block in group) > limit
               for (i, j), limit in available.items()):
            continue
        values = [options(i, adjacency, blocks) for i in uncovered]
        if all(values):
            lower = sum(min(group) for group in values)
            assert lower >= len(uncovered)
            count += 1
            minimum = lower if minimum is None else min(lower, minimum)
    return count, minimum, len(uncovered)


def check_squares():
    for mask in range(15):
        total = 0
        for root in range(4):
            rotated = ((mask >> root) | (mask << (4 - root))) & 15
            total += score(rotated)
        assert total <= 40 * (mask.bit_count() <= 1)
    assert score(0, four_caps=True) == 0


if __name__ == "__main__":
    check_squares()
    for edges in CELL_EDGES:
        print(edges, check_cell(edges))
