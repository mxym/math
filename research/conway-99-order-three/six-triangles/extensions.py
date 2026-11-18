"""Enumerate triangle-to-exterior incidences, including all cyclic shifts."""
import itertools
from collections import Counter, deque
from functools import lru_cache

from check_cores import EDGES, PAIRS, dot, psd

OFFSETS = tuple(range(3))


def support_histograms(c):
    k = [[3 * (i == j) - 3 * c[i][j] + 1 for j in range(6)] for i in range(6)]
    targets = (27,) + tuple(6 * (i == j) + 6 - 5 * c[i][j] - dot(c[i], c[j])
                            for i, j in PAIRS)
    columns = []
    for v in itertools.product(range(2), repeat=6):
        z = [1 - 3 * a for a in v]
        if not psd([r + [a] for r, a in zip(k, z)] + [z + [10]]):
            continue
        if any(v[i] and dot(c[i], v) > 1 for i in range(6)):
            continue
        features = [0] + [q for q, (i, j) in enumerate(PAIRS, 1) if v[i] and v[j]]
        if all(targets[q] for q in features):
            columns.append((tuple(i for i in range(6) if v[i]), features))

    def fill(remaining, needed, histogram):
        if not remaining:
            if not any(needed):
                yield tuple(histogram)
            return
        by_feature = [[j for j in remaining if q in columns[j][1]] for q in range(len(needed))]
        if any(n and not js for n, js in zip(needed, by_feature)):
            return
        q = min((i for i, js in enumerate(by_feature) if js),
                key=lambda i: (len(by_feature[i]), needed[i]))
        j = by_feature[q][0]
        support, features = columns[j]
        rest = remaining - {j}
        upper = min(needed[i] for i in features)
        lower = needed[q] if len(by_feature[q]) == 1 else 0
        for n in range(lower, upper + 1):
            target = list(needed)
            for i in features:
                target[i] -= n
            yield from fill(rest, target, histogram + ([(support, n)] if n else []))

    yield from fill(set(range(len(columns))), targets, [])


def tree_edges(c):
    seen, queue, tree = {0}, deque([0]), []
    while queue:
        i = queue.popleft()
        for j in range(6):
            if c[i][j] and j not in seen:
                seen.add(j)
                queue.append(j)
                tree.append((i, j))
    if len(seen) != 6:
        raise ValueError('the phase normalisation here requires a connected core')
    return tree


def gain_matrices(c):
    tree = {tuple(sorted(e)) for e in tree_edges(c)}
    chords = [(i, j) for i, j in EDGES if c[i][j] and (i, j) not in tree]
    for word in itertools.product(OFFSETS, repeat=len(chords)):
        g = [[0] * 6 for _ in range(6)]
        for (i, j), shift in zip(chords, word):
            g[i][j], g[j][i] = shift, -shift % 3
        yield g


def upper_rows(c, g):
    h = [set() for _ in range(18)]
    for i in range(18):
        h[i].update(3 * (i // 3) + (i + s) % 3 for s in (1, 2))
    for i, j in EDGES:
        if c[i][j]:
            for t in OFFSETS:
                u, v = 3 * i + t, 3 * j + (t + g[i][j]) % 3
                h[u].add(v)
                h[v].add(u)
    return h


def words_for_group(c, g, support):
    for labels in itertools.product(OFFSETS, repeat=max(0, len(support) - 1)):
        w = dict(zip(support, (0,) + labels))
        if all((w[j] - w[i]) % 3 == g[i][j]
               for i, j in itertools.combinations(support, 2) if c[i][j]):
            yield tuple(w.get(i, -1) for i in range(6))


@lru_cache(maxsize=65536)
def compatible(a, b):
    counts = Counter((x - y) % 3 for x, y in zip(a, b) if min(x, y) >= 0)
    return max(counts.values(), default=0) <= 2


def fill_gains(c, g, histogram):
    h = upper_rows(c, g)
    target = tuple(2 - int(3 * j + t in h[3 * i]) - len(h[3 * i] & h[3 * j + t])
                   for i, j in EDGES for t in OFFSETS)
    if min(target) < 0:
        return
    groups = []
    for support, n in histogram:
        words = tuple(words_for_group(c, g, support))
        choose = itertools.combinations if len(support) > 2 else itertools.combinations_with_replacement
        possible = []
        for choice in choose(words, n):
            if any(not compatible(a, b) for a, b in itertools.combinations(choice, 2)):
                continue
            used = Counter(3 * k + (w[j] - w[i]) % 3 for w in choice
                           for k, (i, j) in enumerate(EDGES) if min(w[i], w[j]) >= 0)
            if all(value <= target[k] for k, value in used.items()):
                possible.append((choice, used))
        if not possible:
            return
        groups.append(possible)
    groups.sort(key=len)
    suffix = [set() for _ in range(len(groups) + 1)]
    for k in reversed(range(len(groups))):
        suffix[k] = suffix[k + 1].union(*(used for _, used in groups[k]))

    def extend(k, needed, cols):
        if k == len(groups):
            if not any(needed):
                yield cols
            return
        for choice, used in groups[k]:
            if any(needed[j] < n for j, n in used.items()):
                continue
            rest = tuple(n - used.get(j, 0) for j, n in enumerate(needed))
            if any(n and j not in suffix[k + 1] for j, n in enumerate(rest)):
                continue
            if all(compatible(a, b) for a in cols for b in choice):
                yield from extend(k + 1, rest, cols + choice)

    yield from extend(0, target, ())


def transformations(c, g):
    tree = tree_edges(c)
    edges = [(i, j) for i, j in EDGES if c[i][j]]
    for p in itertools.permutations(range(6)):
        if any(c[i][j] != c[p[i]][p[j]] for i, j in EDGES):
            continue
        inv = [p.index(i) for i in range(6)]
        for sign in (1, -1):
            shifts = [0] * 6
            for i, j in tree:
                shifts[j] = (shifts[i] - sign * g[inv[i]][inv[j]]) % 3
            head = tuple((sign * g[inv[i]][inv[j]] + shifts[j] - shifts[i]) % 3
                         for i, j in edges)
            yield head, inv, sign, shifts


def canonical_columns(cols, inv, sign, shifts):
    result = []
    for col in cols:
        w = [((sign * col[i] + shift) % 3 if col[i] >= 0 else -1)
             for i, shift in zip(inv, shifts)]
        first = next((x for x in w if x >= 0), 0)
        result.append(tuple((x - first) % 3 if x >= 0 else -1 for x in w))
    return tuple(sorted(result))


def representatives(c):
    histograms = list(support_histograms(c))
    reps, total = {}, 0
    for g in gain_matrices(c):
        transforms = list(transformations(c, g))
        head = min(a for a, *_ in transforms)
        maps = [data for a, *data in transforms if a == head]
        for hist in histograms:
            for cols in fill_gains(c, g, hist):
                total += 1
                key = (head, min(canonical_columns(cols, *tr) for tr in maps))
                reps.setdefault(key, (upper_rows(c, g), cols))
    return total, list(reps.values())
