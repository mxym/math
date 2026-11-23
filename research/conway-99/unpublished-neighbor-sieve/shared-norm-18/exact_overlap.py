"""Exact exterior-contact refutations. Pass an executable drat-trim as the argument."""

from collections import Counter, defaultdict
import gzip
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent
SIZE = 27
PAIRS = list(combinations(range(SIZE), 2))
PAIR_ROW = {pair: 1 + SIZE + i for i, pair in enumerate(PAIRS)}


def sites(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


def contact_columns(graph, first_sign=5):
    assert len(graph) == SIZE and all(0 <= row < 1 << SIZE for row in graph)
    assert all(not (row >> i & 1) for i, row in enumerate(graph))
    assert all(graph[i] >> j & 1 == graph[j] >> i & 1 for i, j in PAIRS)
    quotas = [2 - (graph[i] >> j & 1) - (graph[i] & graph[j]).bit_count() for i, j in PAIRS]
    target = [99-SIZE] + [14 - row.bit_count() for row in graph] + quotas
    assert min(target) >= 0
    allowed = [0] * SIZE
    for (i, j), quota in zip(PAIRS, quotas):
        if quota:
            allowed[i] |= 1 << j

    def cliques(word, remaining):
        yield word
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            yield from cliques(word | bit, remaining & allowed[bit.bit_length() - 1])

    closed = [row | (1 << i) for i, row in enumerate(graph)]
    columns = []
    positive = (1 << first_sign) - 1
    negative = 511 ^ positive
    for word in cliques(0, (1 << SIZE) - 1):
        balances = [((word >> start) & positive).bit_count() - ((word >> start) & negative).bit_count()
                    for start in (0, 9, 18)]
        if len(set(balances)) != 1 or any((word & row).bit_count() > 2 for row in closed):
            continue
        members = tuple(sites(word))
        column = [0] + [1+i for i in members] + [PAIR_ROW[p] for p in combinations(members, 2)]
        columns.append((members, column))
    return target, columns


def check_dual(target, columns, sparse):
    y = [0] * len(target)
    for row, value in sparse:
        assert type(row) is int and type(value) is int and 0 <= row < len(target)
        assert y[row] == 0 and value
        y[row] = value
    assert sum(a*b for a, b in zip(y, target)) < 0
    assert all(sum(y[i] for i in column) >= 0 for _, column in columns)


def integer_formula(target, columns, upper_start=None, limit_sites=False):
    from pysat.card import CardEnc, EncType
    from pysat.formula import CNF, IDPool

    variables = IDPool()
    formula = CNF()
    by_row = [[] for _ in target]
    by_triple = defaultdict(list)
    copies_by_word = {}
    for members, column in columns:
        if not members:
            continue
        bound = min(target[i] for i in column)
        if len(members) >= 3:
            bound = min(bound, 1)
        copies = [variables.id() for _ in range(bound)]
        copies_by_word[sum(1 << i for i in members)] = copies
        for earlier, later in zip(copies, copies[1:]):
            formula.append([-later, earlier])
        for i in column:
            by_row[i].extend(copies)
        for triple in combinations(members, 3):
            by_triple[triple].extend(copies)

    if limit_sites:
        if len(by_row[0]) > target[0]:
            formula.extend(CardEnc.atmost(by_row[0], target[0], vpool=variables,
                                          encoding=EncType.totalizer).clauses)
    for i in range(1, len(target)):
        if upper_start is not None and i >= upper_start:
            if len(by_row[i]) > target[i]:
                formula.extend(CardEnc.atmost(by_row[i], target[i], vpool=variables,
                                              encoding=EncType.seqcounter).clauses)
        elif target[i] > len(by_row[i]):
            formula.append([])
        else:
            formula.extend(CardEnc.equals(by_row[i], target[i], vpool=variables,
                                          encoding=EncType.seqcounter).clauses)
    for copies in by_triple.values():
        if len(copies) > 1:
            formula.extend(CardEnc.atmost(copies, 1, vpool=variables,
                                          encoding=EncType.seqcounter).clauses)

    return formula, copies_by_word


def check_integer(target, columns, drat_trim, upper_start=None, limit_sites=False, allow_sat=False,
                  neighbor_clauses=None, solver_name='g4'):
    from pysat.solvers import Solver

    formula, copies = integer_formula(target, columns, upper_start, limit_sites)
    if neighbor_clauses is not None:
        formula.extend(neighbor_clauses(copies))
    with Solver(name=solver_name, bootstrap_with=formula, with_proof=True) as solver:
        if solver.solve():
            if allow_sat:
                return True
            raise AssertionError('unexpected feasible exterior contact system')
        with TemporaryDirectory() as tmp:
            cnf = Path(tmp)/'case.cnf'
            proof = Path(tmp)/'case.drat'
            formula.to_file(str(cnf))
            proof.write_text('\n'.join(solver.get_proof()) + '\n')
            check = subprocess.run([drat_trim, cnf, proof], check=True, capture_output=True)
            assert b's VERIFIED' in check.stdout
    return False


def main(drat_trim):
    with gzip.open(HERE/'cores.json.gz', 'rt') as file:
        families = json.load(file)
    with gzip.open(HERE/'exact-duals.json.gz', 'rt') as file:
        proofs = json.load(file)
    assert len(families) == len(proofs) == 2
    for i, (cores, certificates) in enumerate(zip(families, proofs)):
        assert len(cores) == len(certificates) == (1578, 4487)[i]
        stats = Counter()
        for graph, dual in zip(cores, certificates):
            target, columns = contact_columns(graph)
            if dual is None:
                check_integer(target, columns, drat_trim)
                stats['DRAT'] += 1
            else:
                check_dual(target, columns, dual)
                stats['integer inequalities'] += 1
        print(i, dict(stats), flush=True)
        assert (stats['integer inequalities'], stats['DRAT']) == ((1550, 28), (4313, 174))[i]


if __name__ == '__main__':
    main(sys.argv[1])
