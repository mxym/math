"""Replay the exterior-contact screen on the archived 27-vertex inputs."""

import argparse
from collections import Counter, defaultdict
import gzip
from itertools import combinations
import json
from pathlib import Path

import numpy as np
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


SIZE = 27
OUTSIDE = 99 - SIZE
PAIRS = list(combinations(range(SIZE), 2))


def sites(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def contact_words(graph, pair_quota):
    allowed = [0] * SIZE
    for (i, j), remaining in zip(PAIRS, pair_quota):
        if remaining:
            allowed[i] |= 1 << j
    closed = [row | (1 << i) for i, row in enumerate(graph)]

    def extend(word, candidates, seen_once, seen_twice, balance):
        while candidates:
            bit = candidates & -candidates
            candidates ^= bit
            i = bit.bit_length() - 1
            if closed[i] & seen_twice:
                continue
            next_balance = list(balance)
            next_balance[i // 9] += 1 if i % 9 < 5 else -1
            if next_balance[0] == next_balance[1] == next_balance[2]:
                yield word | bit
            yield from extend(word | bit, candidates & allowed[i],
                              seen_once | closed[i], seen_twice | (seen_once & closed[i]),
                              next_balance)

    yield 0
    yield from extend(0, (1 << SIZE) - 1, 0, 0, [0, 0, 0])


def quotas(graph):
    assert len(graph) == SIZE and all(0 <= row < 1 << SIZE for row in graph)
    assert all(not (row >> i & 1) for i, row in enumerate(graph))
    assert all((graph[i] >> j & 1) == (graph[j] >> i & 1) for i, j in PAIRS)
    pair_quota = [2 - (graph[i] >> j & 1) - (graph[i] & graph[j]).bit_count() for i, j in PAIRS]
    target = [OUTSIDE] + [14 - row.bit_count() for row in graph] + pair_quota
    assert min(target) >= 0
    words = list(contact_words(graph, pair_quota))
    pair_index = {pair: i + 1 + SIZE for i, pair in enumerate(PAIRS)}
    columns = []
    for word in words:
        members = list(sites(word))
        columns.append([0] + [1 + i for i in members]
                       + [pair_index[pair] for pair in combinations(members, 2)])
    return words, columns, target


def classify(graph):
    words, columns, target = quotas(graph)
    row_ids = [i for column in columns for i in column]
    col_ids = [j for j, column in enumerate(columns) for _ in column]
    matrix = coo_matrix((np.ones(len(row_ids)), (row_ids, col_ids)),
                        shape=(len(target), len(words))).tocsc()
    lp = linprog(np.zeros(len(words)), A_eq=matrix, b_eq=target, bounds=(0, None))
    if lp.status == 2:
        return 'LP infeasible'
    if not lp.success:
        raise RuntimeError(lp.message)

    pool = IDPool()
    clause_rows = [[] for _ in target]
    triples = defaultdict(list)
    with Solver(name='cadical195') as solver:
        for word, column in zip(words, columns):
            if not word:
                continue  # Empty contacts fill unused exterior places.
            bound = min(target[i] for i in column)
            if word.bit_count() >= 3:
                bound = min(bound, 1)
            copies = [pool.id() for _ in range(bound)]
            for j in range(1, bound):
                solver.add_clause([-copies[j], copies[j - 1]])
            for row in column:
                clause_rows[row].extend(copies)
            for triple in combinations(sites(word), 3):
                triples[triple].extend(copies)

        def constrain(literals, count, exact):
            if exact and count > len(literals):
                solver.add_clause([])
            elif exact or count < len(literals):
                encode = CardEnc.equals if exact else CardEnc.atmost
                solver.append_formula(encode(literals, count, vpool=pool,
                                             encoding=EncType.seqcounter).clauses)

        for row, (literals, count) in enumerate(zip(clause_rows, target)):
            constrain(literals, count, exact=(row != 0))
        for literals in triples.values():
            constrain(literals, 1, exact=False)
        return 'integer feasible' if solver.solve() else 'SAT unsatisfiable'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', type=int, choices=(0, 1))
    parser.add_argument('--case', type=int, help='zero-based index in the selected family')
    args = parser.parse_args()
    with gzip.open(Path(__file__).with_name('cores.json.gz'), 'rt') as stream:
        families = json.load(stream)
    assert list(map(len, families)) == [1578, 4487]
    if args.case is not None:
        if args.family is None or not 0 <= args.case < len(families[args.family]):
            parser.error('--case requires a valid index and --family')
        print(classify(families[args.family][args.case]))
        return
    for family in range(2) if args.family is None else [args.family]:
        print(family, dict(Counter(map(classify, families[family]))), flush=True)


if __name__ == '__main__':
    main()
