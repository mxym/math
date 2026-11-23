"""Reconstruct the three-label overlap catalogues and verify their exterior obstructions."""

import argparse
from collections import Counter
from functools import partial
import gzip
from itertools import combinations
import json
from multiprocessing import get_context
from pathlib import Path

import numpy as np
import pynauty

from enumerate_cores import add_edge, gluings, mask, members
from exact_overlap import check_dual, check_integer
from one_panel import contact_test, wings
from panel_heights import canonical_rows


HERE = Path(__file__).resolve().parent
THIRTEEN = (15,19,21,26)
TWELVE = {(15,3,21,22):(406,201), (15,3,21,26):(12669,5496), (15,3,21,28):(4951,4288)}


def unrooted_key(graph):
    # Three extra vertices distinguish the panels while allowing all six permutations.
    decorated = list(graph) + [0,0,0]
    for i in range(27):
        add_edge(decorated, i, 27+i//9)
    small = {i for i in range(27) if i%9 < 4}
    colors = [small, set(range(27))-small, {27,28,29}]
    return pynauty.certificate(pynauty.Graph(30, adjacency_dict={
        i:list(members(row)) for i,row in enumerate(decorated)}, vertex_coloring=colors))


def reconstruct(genbg, edges):
    if edges == 13:
        small = canonical_rows(THIRTEEN)
        charts = [g for g in wings(genbg, THIRTEEN)
                  if canonical_rows([(g[i] >> 13) & 31 for i in range(9,13)]) == small]
        assert len(charts) == 104
        keys = {unrooted_key(g) for g in gluings(charts, 4)}
        assert len(keys) == 1959
        return keys

    keys = set()
    for shape, expected in TWELVE.items():
        local = set()
        count = 0
        for graph in gluings(wings(genbg, shape), 4):
            count += 1
            local.add(unrooted_key(graph))
        assert (count, len(local)) == expected
        keys.update(local)
    assert len(keys) == 9106
    return keys

def necessary_neighbor_clauses(graph, columns, copies, extended):
    words = [mask(sites) for sites, _ in columns]
    words_array = np.asarray(words)
    has_site = [((words_array >> i) & 1).astype(bool) for i in range(27)]
    sides = [(15 << (9*((j+1)%3))) | (496 << (9*((j+2)%3))) for j in range(3)]
    heights = np.array([[(side & word).bit_count() for word in words] for side in sides])
    remaining = [[2-(word >> i & 1)-(word & row).bit_count() for i,row in enumerate(graph)]
                 for word in words]
    saturated = np.array([mask(i for i,v in enumerate(row) if not v) for row in remaining])
    for k, word in enumerate(words):
        if not copies.get(word):
            continue
        possible = ((saturated[k] & words_array) == 0) & ((saturated & word) == 0)
        for h in heights:
            if h[k] >= 2:
                possible &= h < (2 if h[k] == 3 else 3)
        for i,j in combinations(members(word), 2):
            possible &= ~(has_site[i] & has_site[j])
        for j, need in enumerate(remaining[k]):
            if not need:
                continue
            options = [v for idx in np.flatnonzero(possible & has_site[j])
                       for v in copies.get(words[idx], ())]
            if (not extended and len(options) > 12) or (need == 2 and len(options) > 28):
                continue
            if len(options) < need:
                yield [-copies[word][0]]
                break
            for subset in combinations(options, len(options)-need+1):
                yield [-copies[word][0], *subset]


def verify_case(case, drat_trim):
    graph, proof = case
    target, columns, first_upper = contact_test(graph, 4)
    if isinstance(proof, list):
        assert all(i < first_upper or value >= 0 for i,value in proof)
        check_dual(target, columns, proof)
        return 'integer inequality'
    assert proof in ('g4', 'cadical195')
    def clauses(copies):
        return necessary_neighbor_clauses(graph, columns, copies, extended=proof == 'cadical195')
    check_integer(target, columns, drat_trim, upper_start=first_upper,
                  neighbor_clauses=clauses, solver_name=proof)
    return 'DRAT'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--genbg', default='genbg')
    parser.add_argument('--drat-trim', required=True)
    parser.add_argument('--edges', type=int, choices=(12,13), help='verify just one catalogue')
    parser.add_argument('--jobs', type=int, default=1, help='independent verification processes')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    for edges in ([args.edges] if args.edges else (12,13)):
        archive, separators, refutations = {
            12: ('three-label-twelve-edge-cases.json.gz', 8929, 177),
            13: ('thirteen-edge-cases.json.gz', 1181, 778),
        }[edges]
        with gzip.open(HERE/archive, 'rt') as stream:
            cases = json.load(stream)
        assert len(cases) == separators+refutations
        assert {unrooted_key(g) for g, proof in cases} == reconstruct(args.genbg, edges)
        check = partial(verify_case, drat_trim=args.drat_trim)
        if args.jobs == 1:
            totals = Counter(map(check, cases))
        else:
            with get_context('spawn').Pool(args.jobs) as pool:
                totals = Counter(pool.imap_unordered(check, cases, chunksize=2))
        assert totals == {'integer inequality':separators, 'DRAT':refutations}
        print(edges, 'internal edges:', dict(totals), flush=True)


if __name__ == '__main__':
    main()
