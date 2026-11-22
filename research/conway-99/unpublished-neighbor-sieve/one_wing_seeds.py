"""Enumerate first exterior rows at a clean root, up to the first wing's relabelings."""
from itertools import combinations, permutations, product


ROOT = (0, 2)
LABELS = tuple(range(12))
PAIRS = tuple((a, b) for a, b in combinations(LABELS, 2) if (a ^ 1) != b)
INDEX = {edge: i for i, edge in enumerate(PAIRS)}


def group():
    for a, b in (ROOT, ROOT[::-1]):
        for axes in permutations(range(2, 6)):
            for shifts in product((0, 1), repeat=4):
                tail = tuple(2*j + (side ^ s) for j, s in zip(axes, shifts) for side in (0, 1))
                yield (a, a+1, b, b+1, *tail)


def prescribed_rows(support):
    """Use the least as yet unprocessed label to emit each graph just once."""
    remaining = [2 - int(i < 4) - int(i in support) for i in LABELS]
    chosen = []

    def visit(i):
        while i < 12 and remaining[i] == 0:
            i += 1
        if i == 12:
            yield tuple(chosen)
            return
        available = [j for j in range(i+1, 12)
                     if remaining[j] and (i, j) in INDEX and (i, j) != ROOT]
        for adjacent in combinations(available, remaining[i]):
            for j in adjacent:
                remaining[j] -= 1
                chosen.append(INDEX[i, j])
            yield from visit(i+1)
            for j in adjacent:
                remaining[j] += 1
                chosen.pop()

    yield from visit(0)


def seed_types():
    group_elements = list(group())
    seen = set()
    for support in combinations(sorted(set(LABELS) - set(ROOT)), 4):
        if support in seen:
            continue
        def image(g):
            return tuple(sorted(g[i] for i in support))
        orbit = {image(g) for g in group_elements}
        seen.update(orbit)
        stabilizer = [g for g in group_elements if image(g) == support]
        actions = [[INDEX[tuple(sorted((g[a], g[b])))] for a, b in PAIRS] for g in stabilizer]
        covered, representatives = set(), []
        labeled = 0
        for row in prescribed_rows(support):
            labeled += 1
            if row not in covered:
                representatives.append(row)
                covered.update(tuple(sorted(g[j] for j in row)) for g in actions)
        assert len(covered) == labeled
        yield support, len(orbit), labeled, representatives


if __name__ == "__main__":
    count = labeled = 0
    for support, multiplicity, row_count, rows in seed_types():
        print(support, multiplicity, row_count, len(rows))
        labeled += multiplicity * row_count
        count += len(rows)
    assert (labeled, count) == (4732468, 6727)
    print("Labeled rows with supports:", labeled, "orbits:", count)
