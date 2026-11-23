"""Enumerate rooted charts directly from the four degree equations at their pair labels."""

from collections import Counter
from functools import lru_cache
import gzip
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from pathlib import Path

from enumerate_cores import LABEL_SETS, add_edge, certificate, gluings, mask, members, valid


@lru_cache(None)
def column_permutations(labels):
    # Equal contact masks are the only freedom left in ordering the four columns.
    return [[mask(j for j, i in enumerate(order) if v >> i & 1) for v in range(16)]
            for order in permutations(range(4)) if tuple(labels[i] for i in order) == labels]


def matrix_completions(left, right):
    budgets = [4 - v.bit_count() for v in right]
    choices = [[mask(js) for js in combinations(range(4), 4 - v.bit_count())] for v in left]

    def extend(previous):
        i = len(previous)
        if i == 5:
            yield previous
            return
        forbidden = mask(j for j, count in enumerate(budgets) if count == 0)
        required = mask(j for j, count in enumerate(budgets) if count == 5 - i)
        for row in choices[i]:
            if row & forbidden or row & required != required:
                continue
            if i and left[i] == left[i-1] and previous[-1] > row:
                continue
            entries = list(members(row))
            for j in entries:
                budgets[j] -= 1
            yield from extend(previous + (row,))
            for j in entries:
                budgets[j] += 1
    return extend(())


def graph_of(labels, left, right, matrix):
    graph = [0] * 18
    for i, parents in enumerate((range(4), *labels)):
        for j in parents:
            add_edge(graph, i, 5+j)
    for start, offset, rows in ((9, 0, left), (14, 5, right), (9, 14, matrix)):
        for i, row in enumerate(rows):
            for j in members(row):
                add_edge(graph, start+i, offset+j)
    return graph


def direct_charts(labels):
    # The negative neighbors of the root are fixed. Its four further marked
    # pair labels must each receive exactly two of the five remaining negatives.
    left_choices = set()
    for ends in product(combinations(range(5), 2), repeat=4):
        if any(len(set(labels[i]) & set(labels[j])) + len(set(ends[i]) & set(ends[j])) > 2
               for i, j in combinations(range(4), 2)):
            continue
        left_choices.add(tuple(sorted(mask(i+1 for i, pair in enumerate(ends) if j in pair)
                                      for j in range(5))))
    # The four remaining positives see zero, one, or an as-yet-unused pair
    # of the root's four neighbors.
    omitted = set(combinations(range(4), 2)) - set(labels)
    words = sorted({0, 1, 2, 4, 8} | {mask(pair) for pair in omitted})
    degrees = Counter(v for pair in labels for v in pair)
    right_choices = [rows for rows in combinations_with_replacement(words, 4)
                     if all(sum((v >> j) & 1 for v in rows) == 3-degrees[j] for j in range(4))]
    seen = set()
    for left, right in product(left_choices, right_choices):
        for matrix in matrix_completions(left, right):
            if not valid(graph_of(labels, left, right, matrix)):
                continue
            normal = min(tuple(v for _, v in sorted(zip(left, (table[row] for row in matrix))))
                         for table in column_permutations(right))
            seen.add((left, right, normal))
    return [graph_of(labels, *chart) for chart in sorted(seen)]


def main():
    with gzip.open(Path(__file__).with_name('cores.json.gz'), 'rt') as f:
        archive = json.load(f)
    for i, labels in enumerate(LABEL_SETS):
        wings = direct_charts(labels)
        seen = set()
        count = 0
        for graph in gluings(wings):
            seen.add(certificate(graph))
            count += 1
        assert seen == set(map(certificate, archive[i]))
        summary = len(wings), count, len(seen)
        assert summary == ((434, 2463, 1578), (616, 19416, 4487))[i]
        print(i, summary, flush=True)


if __name__ == '__main__':
    main()
