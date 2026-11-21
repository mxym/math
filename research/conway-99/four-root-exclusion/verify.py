"""Exclude four orthogonal Fano configurations using only Python's standard library."""

from collections import Counter
from itertools import combinations, permutations, product


GROUPS = range(4)
ORDERED = list(permutations(GROUPS, 2))
LABELS = ["o", "a", "b"] + [(t, i, j) for t in "pnd" for i, j in ORDERED]
INDEX = {s: k for k, s in enumerate(LABELS)}
SIGNS = [set(), {(1, i) for i in GROUPS}, {(-1, i) for i in GROUPS}]
for kind, i, j in LABELS[3:]:
    if kind == "p":
        SIGNS.append({(1, i)})
    elif kind == "n":
        SIGNS.append({(-1, i)})
    else:
        SIGNS.append({(1, i), (-1, j)})


def join(graph, x, y):
    a, b = INDEX[x], INDEX[y]
    graph[a].add(b)
    graph[b].add(a)


def graphs(perms):
    graph = [set() for _ in LABELS]
    for x, y in (("o", "a"), ("o", "b"), ("a", "b")):
        join(graph, x, y)
    for i, j in ORDERED:
        p, n = ("p", i, j), ("n", i, j)
        join(graph, "a", n)
        join(graph, "b", p)
        join(graph, p, ("p", j, i))
        join(graph, n, ("n", j, i))
        join(graph, p, ("n", i, perms[i][j]))
        for k in GROUPS:
            if k not in (i, j):
                join(graph, n, ("d", i, k))
                join(graph, p, ("d", k, i))

    # Each double already has four single neighbors. Enumerate its four
    # remaining neighbors as a subset of the other eleven doubles.
    doubles = [INDEX["d", i, j] for i, j in ORDERED]
    choices = {}
    for v in doubles:
        required = {}
        for s in (-1, 1):
            for i in GROUPS:
                required[s, i] = (0 if (s, i) in SIGNS[v] else
                                  4 if (-s, i) in SIGNS[v] else 1)
        valid = []
        same_side_singles = [u for u in range(3, 27) if SIGNS[u] & SIGNS[v]]
        candidates = [u for u in doubles if u != v and not SIGNS[u] & SIGNS[v]]
        for four in combinations(candidates, 4):
            neighbors = graph[v] | set(four)
            if any(sum(sign in SIGNS[u] for u in neighbors) != count
                   for sign, count in required.items()):
                continue
            # Each same-side pair has both common neighbors in the opposite side
            # of its Fano configuration, hence both in these 39 vertices.
            if any(len(neighbors & graph[u]) != 2 for u in same_side_singles):
                continue
            valid.append(frozenset(four))
        if not valid:
            return
        choices[v] = valid

    def extend(pos, rows):
        if pos == len(doubles):
            yield [g | rows.get(i, set()) for i, g in enumerate(graph)]
            return
        v = doubles[pos]
        for row in choices[v]:
            if all((u in row) == (v in r) for u, r in rows.items()):
                rows[v] = row
                yield from extend(pos + 1, rows)
                del rows[v]

    yield from extend(0, {})


def residual(graph, x, y):
    return 2 - int(y in graph[x]) - len(graph[x] & graph[y])


def double_blocks(graph):
    v = INDEX["d", 0, 1]
    blocks = []
    for i in (2, 3):
        eligible = [u for u in range(len(graph)) if u != v
                    and not any(j == i for _, j in SIGNS[u])]
        for four in combinations(eligible, 4):
            block = frozenset((v, *four))
            signs = [s for u in block for s in SIGNS[u]]
            if len(signs) != 6 or len(set(signs)) != 6:
                continue
            if any(residual(graph, x, y) < 1 for x, y in combinations(block, 2)):
                continue
            if any(len(neighbors & block) > 2 - int(x in block)
                   for x, neighbors in enumerate(graph)):
                continue
            blocks.append((i, block))
    return v, blocks


def count_neighborhoods(graph, v, blocks, check_overlap):
    # The last four counters specify how many neighbors come from each Y_i.
    need = [residual(graph, v, u) if u != v else 0 for u in range(39)] + [0, 0, 3, 3]
    columns = [(block - {v}) | {39 + i} for i, block in blocks]
    uses = [sum(1 << j for j, c in enumerate(columns) if k in c) for k in range(43)]
    conflict = [sum(1 << j for j, (_, c) in enumerate(blocks) if len(b & c) > 2)
                for _, b in blocks]

    def search(need, available):
        positive = [k for k, n in enumerate(need) if n]
        if not positive:
            return 1
        for k, n in enumerate(need):
            if n == 0:
                available &= ~uses[k]
        k = min(positive, key=lambda i: (available & uses[i]).bit_count() - need[i])
        options = available & uses[k]
        if options.bit_count() < need[k]:
            return 0
        total = 0
        while options:
            bit = options & -options
            j = bit.bit_length() - 1
            options ^= bit
            available ^= bit
            remaining = need.copy()
            for i in columns[j]:
                remaining[i] -= 1
            following = available & ~conflict[j] if check_overlap else available
            total += search(remaining, following)
        return total

    return search(need, (1 << len(columns)) - 1)


def main():
    totals = Counter()
    orders = [sorted(set(GROUPS) - {i}) for i in GROUPS]
    for values in product(*(permutations(row) for row in orders)):
        perms = [dict(zip(row, value)) for row, value in zip(orders, values)]
        totals["permutation choices"] += 1
        for graph in graphs(perms):
            totals["symmetric double adjacencies"] += 1
            if any(residual(graph, x, y) < 0 for x, y in combinations(range(39), 2)):
                continue
            totals["cores"] += 1
            assert all(perms[i][j] == j for i, j in ORDERED)
            v, blocks = double_blocks(graph)
            assert len(blocks) == 70
            assert count_neighborhoods(graph, v, blocks, False) == 3841
            assert count_neighborhoods(graph, v, blocks, True) == 0
    print(dict(totals))
    assert totals == {"permutation choices": 1296, "symmetric double adjacencies": 4,
                      "cores": 1}
    print("Double site d_01: 70 candidate blocks, 3841 relaxed neighborhoods, 0 valid.")


if __name__ == "__main__":
    main()
