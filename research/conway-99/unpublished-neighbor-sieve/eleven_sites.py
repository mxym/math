"""Enumerate admissible four-regular graphs on eleven sites, with a fixed root."""

from collections import Counter
from itertools import combinations, combinations_with_replacement

TEMPLATES = (
    (1232,1376,1696,960,1793,390,523,45,58,92,23),
    (1352,1616,864,897,1410,1668,135,120,29,46,51),
)


def add_edge(rows, i, j):
    rows[i] |= 1 << j
    rows[j] |= 1 << i


def pair_quotas(rows):
    return all((rows[i] & rows[j]).bit_count() + ((rows[i] >> j) & 1) <= 2
               for i, j in combinations(range(11), 2))


def finish(rows, i=5):
    if i == 11:
        yield tuple(rows)
        return
    deficit = 4 - rows[i].bit_count()
    possible = [j for j in range(i + 1, 11) if rows[j].bit_count() < 4]
    for chosen in combinations(possible, deficit):
        updated = rows.copy()
        for j in chosen:
            add_edge(updated, i, j)
        if pair_quotas(updated):
            yield from finish(updated, i + 1)


def rooted_candidates():
    masks = [m for m in range(16) if m.bit_count() <= 2]
    for mates in range(3):
        base = [0] * 11
        for i in range(1, 5):
            add_edge(base, 0, i)
        for j in range(mates):
            add_edge(base, 2*j+1, 2*j+2)
        degrees = [4 - base[i].bit_count() for i in range(1, 5)]
        for words in combinations_with_replacement(masks, 6):
            if any(sum((m >> j) & 1 for m in words) != d for j, d in enumerate(degrees)):
                continue
            rows = base.copy()
            for i, word in enumerate(words, 5):
                for j in range(4):
                    if word & (1 << j):
                        add_edge(rows, i, j + 1)
            if pair_quotas(rows):
                yield from finish(rows)


def isomorphic(rows, target):
    def signature(g, i):
        return tuple(sorted(((g[i] >> j) & 1, (g[i] & g[j]).bit_count())
                            for j in range(11) if j != i))
    source = [signature(rows, i) for i in range(11)]
    dest = [signature(target, i) for i in range(11)]
    possible = [[j for j in range(11) if dest[j] == key] for key in source]
    order = sorted(range(11), key=lambda i: len(possible[i]))
    def extend(index, mapped, used):
        if index == 11:
            return True
        i = order[index]
        for j in possible[i]:
            if j in used or any(((target[j] >> v) ^ (rows[i] >> u)) & 1
                                for u, v in mapped):
                continue
            if extend(index + 1, mapped + [(i,j)], used | {j}):
                return True
        return False
    return extend(0, [], set())


def shell_rank(rows):
    shell = list(rows)
    for i, j in combinations(range(11), 2):
        demand = 2 - ((rows[i] >> j) & 1) - (rows[i] & rows[j]).bit_count()
        for _ in range(demand):
            k = len(shell)
            shell.append(0)
            add_edge(shell, i, k)
            add_edge(shell, j, k)
    assert len(shell) == 33
    matrix = [[(27*(i == j) + 1 - 9*((row >> j) & 1)) % 7 for j in range(33)]
              for i, row in enumerate(shell)]
    rank = 0
    for col in range(33):
        pivot = next((i for i in range(rank, 33) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        row = matrix[rank]
        inverse = pow(row[col], -1, 7)
        for i in range(rank + 1, 33):
            factor = matrix[i][col] * inverse
            matrix[i] = [(a - factor*b) % 7 for a, b in zip(matrix[i], row)]
        rank += 1
    return rank


if __name__ == "__main__":
    assert not isomorphic(*TEMPLATES)
    counts = Counter()
    for rows in rooted_candidates():
        hits = [i for i, target in enumerate(TEMPLATES) if isomorphic(rows, target)]
        assert len(hits) == 1
        counts[hits[0]] += 1
    assert len(counts) == 2 and all(shell_rank(graph) == 32 for graph in TEMPLATES)
    print("Rooted enumeration hits for the two unrooted templates:", sorted(counts.items()))
