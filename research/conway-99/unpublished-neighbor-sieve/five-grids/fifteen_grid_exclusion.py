"""Reconstruct the fifteen-grid cases and test their regular common-neighbor blocks."""

import argparse
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

from complete_point import perfect_matchings
from fifteen_grids import CELLS, DIRTY, REGULAR, disjoint, pair_test


def site_profiles(cell):
    neighbors = [b for b in range(21) if disjoint(cell, b)]

    def allowed(b, c):
        return disjoint(b, c) or (b in DIRTY and c in DIRTY)

    matchings = list(perfect_matchings(neighbors, allowed))
    counts_to_sites = defaultdict(list)
    for sites in combinations_with_replacement(matchings, 4):
        counts = defaultdict(int)
        for site in sites:
            for b, c in site:
                counts[tuple(sorted((cell, b, c)))] += 1
        if any(n % 2 and any(pair_test(a, b) for a, b in combinations(t, 2))
               for t, n in counts.items()):
            continue
        counts_to_sites[tuple(sorted(counts.items()))].append(sites)
    return counts_to_sites


def agree(a, row, b, other):
    return tuple((t, n) for t, n in row if b in t) == tuple(
        (t, n) for t, n in other if a in t)


def profiles():
    data = {a: site_profiles(a) for a in REGULAR}

    def visit(domains, chosen):
        if not domains:
            # A triangle count profile determines the unordered four site matchings
            # uniquely in every retained case. All labelings are allowed downstream.
            assert all(len(data[a][r]) == 1 for a, r in chosen.items())
            yield tuple(sorted(chosen.items()))
            return
        a = min(domains, key=lambda c: len(domains[c]))
        for row in domains[a]:
            rest = {b: [r for r in rows if agree(a, row, b, r)]
                    for b, rows in domains.items() if b != a}
            if all(rest.values()):
                yield from visit(rest, chosen | {a: row})

    cases = set(visit({a: list(rows) for a, rows in data.items()}, {}))
    assert len(cases) == 90
    remaining = cases.copy()
    while remaining:
        key = min(remaining)
        orbit = set()
        for p, q, r in product(permutations(range(2)), permutations(range(2, 5)),
                               permutations(range(5, 7))):
            labels = p + q + r
            cell_map = [CELLS.index(tuple(sorted(labels[i] for i in c))) for c in CELLS]
            orbit.add(tuple(sorted(
                (cell_map[a], tuple(sorted((tuple(sorted(cell_map[c] for c in t)), n)
                                          for t, n in row))) for a, row in key)))
        assert orbit <= remaining
        remaining -= orbit
        yield len(orbit), {a: data[a][row][0] for a, row in key}


def formula(sites):
    ids = IDPool()
    cnf = CNF()

    def count(lits, n):
        cnf.extend(CardEnc.equals(list(lits), n, vpool=ids, encoding=EncType.seqcounter))

    def edge(a, x, b, y):
        return ids.id(('edge',) + tuple(sorted(((a, x), (b, y)))))

    def conjunction(p, q):
        v = ids.id(('conjunction', min(p, q), max(p, q)))
        cnf.extend(([-v, p], [-v, q], [v, -p, -q]))
        return v

    for a, b in combinations(range(21), 2):
        if not disjoint(a, b) or (a not in sites and b not in sites):
            continue
        for x in range(4):
            count([edge(a, x, b, y) for y in range(4)], 1)
            count([edge(a, y, b, x) for y in range(4)], 1)

    for a, rows in sites.items():
        labelings = sorted(set(permutations(rows)))
        selectors = [ids.id(('labeling', a, i)) for i in range(len(labelings))]
        count(selectors, 1)
        for selector, labeling in zip(selectors, labelings):
            for x, matching in enumerate(labeling):
                for b, c in matching:
                    # If A_x sees B_y and C_z, then B_y must see C_z.
                    # Impose only if all three matchings are present in this formula.
                    if b not in sites and c not in sites:
                        continue
                    assert disjoint(b, c)
                    for y, z in product(range(4), repeat=2):
                        cnf.append([-selector, -edge(a, x, b, y), -edge(a, x, c, z),
                                    edge(b, y, c, z)])

    for a, b in combinations(REGULAR, 2):
        thirds = [c for c in range(21) if disjoint(a, c) and disjoint(b, c)]
        shared = set(CELLS[a]) & set(CELLS[b])
        for x, y in product(range(4), repeat=2):
            paths = [conjunction(edge(a, x, c, z), edge(b, y, c, z))
                     for c in thirds for z in range(4)]
            if shared:
                axis, = shared
                same_parent = ((x >> CELLS[a].index(axis)) & 1) == (
                    (y >> CELLS[b].index(axis)) & 1)
                count(paths, 2 - int(same_parent))
            else:
                paths.extend(edge(a, x ^ step, b, y) for step in (1, 2))
                paths.extend(edge(a, x, b, y ^ step) for step in (1, 2))
                paths.append(edge(a, x, b, y))
                count(paths, 2)
    return cnf


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proof-dir', type=Path)
    args = parser.parse_args()
    if args.proof_dir:
        args.proof_dir.mkdir(parents=True, exist_ok=True)
    sizes = []
    for i, (size, sites) in enumerate(profiles(), start=1):
        cnf = formula(sites)
        with Solver(name='g4', bootstrap_with=cnf, with_proof=bool(args.proof_dir)) as solver:
            assert solver.solve() is False
            if args.proof_dir:
                cnf.to_file(str(args.proof_dir / f'case-{i}.cnf'))
                (args.proof_dir / f'case-{i}.drat').write_text(
                    '\n'.join(solver.get_proof()) + '\n')
        sizes.append(size)
        print(f'Case {i}, orbit size {size}: contradiction.', flush=True)
    assert sorted(sizes) == [6, 6, 6, 12, 12, 12, 12, 24]
    print('All 90 profiles excluded.')


if __name__ == '__main__':
    main()
