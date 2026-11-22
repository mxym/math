"""Exact enumeration for the triangle-array obstruction. Requires NumPy."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations, product

import numpy as np


PERMS = tuple(permutations(range(3)))
LINES = [(3*i, 3*i+1, 3*i+2) for i in range(3)] + [(i, i+3, i+6) for i in range(3)]
TRANSVERSALS = [tuple(3*i+j for i, j in enumerate(perm)) for perm in PERMS]
FREE_EDGES = [(1, 4), (1, 7), (2, 5), (2, 8)]


def inverse(perm):
    return tuple(perm.index(i) for i in range(3))


def compose(left, right):
    return tuple(left[i] for i in right)


def transport(key):
    steps = {}
    generators = [PERMS[0]]*8 + [PERMS[i] for i in key]
    for (p, q, r), u, v in zip(LINES, generators[::2], generators[1::2]):
        for a, b, perm in [(p, q, u), (p, r, v), (q, r, compose(v, inverse(u)))]:
            steps[a, b] = perm
            steps[b, a] = inverse(perm)
    return steps


def relabelings(steps):
    for rows, cols, transpose in product(PERMS, PERMS, (False, True)):
        base = [3*cols[j]+rows[i] if transpose else 3*rows[i]+cols[j]
                for i, j in product(range(3), repeat=2)]
        for origin in PERMS:
            frames = {0: origin}
            for p, q in [(0, 3), (0, 6), (0, 1), (0, 2), (3, 4), (3, 5), (6, 7), (6, 8)]:
                frames[q] = compose(steps[base[p], base[q]], frames[p])
            key = tuple(PERMS.index(compose(inverse(frames[q]),
                        compose(steps[base[p], base[q]], frames[p]))) for p, q in FREE_EDGES)
            yield key, tuple(3*base[p]+frames[p][i] for p, i in product(range(9), range(3)))


def shell_matrix(steps):
    shell = np.zeros((27, 27), dtype=np.int16)
    for a, b in combinations(range(27), 2):
        p, q = a//3, b//3
        shell[a, b] = shell[b, a] = p == q or ((p, q) in steps and steps[p, q][a%3] == b%3)
    assert np.all(shell.sum(axis=0) == 6)
    return shell


@cache
def tables(xy, xz, yz):
    slices = []
    for x in range(3):
        choices = [combinations(range(3), xy[3*x+y]) for y in range(3)]
        slices.append([frozenset((y, z) for y, row in enumerate(rows) for z in row)
                       for rows in product(*choices)
                       if all(sum(z in row for row in rows) == xz[3*x+z] for z in range(3))])
    return [tuple((x, y, z) for x, slc in enumerate(slc_tuple) for y, z in sorted(slc))
            for slc_tuple in product(*slices)
            if all(sum((y, z) in slc for slc in slc_tuple) == yz[3*y+z]
                   for y, z in product(range(3), repeat=2))]


def boundary_options(shell):
    missing = 2-shell@ shell
    def marginal(p, q):
        return tuple(missing[3*p:3*p+3, 3*q:3*q+3].flat)
    options = []
    for p, q, r in TRANSVERSALS:
        local = tables(marginal(p, q), marginal(p, r), marginal(q, r))
        options.append([frozenset((3*p+i, 3*q+j, 3*r+k) for i, j, k in choice)
                        for choice in local])
    return options


def uncovered_squares(shell):
    neighbors = [set(np.flatnonzero(row)) for row in shell]
    def cap(a, b):
        point, = neighbors[a] & neighbors[b]
        return point
    uncovered = 0
    for a, c in combinations(range(27), 2):
        corners = neighbors[a] & neighbors[c]
        if shell[a, c] or len(corners) != 2 or a > min(corners):
            continue
        b, d = sorted(corners)
        if not (shell[cap(a, b), cap(c, d)] or shell[cap(b, c), cap(d, a)]):
            uncovered += 1
    return uncovered


def boundaries(options, automorphisms):
    seen = set()
    for indices in product(*(range(len(opts)) for opts in options)):
        if indices in seen:
            continue
        selected = [opts[i] for opts, i in zip(options, indices)]
        for action in automorphisms:
            image = [-1]*6
            for triple_set in selected:
                moved = frozenset(tuple(sorted(action[v] for v in row)) for row in triple_set)
                base = tuple(v//3 for v in next(iter(moved)))
                t = TRANSVERSALS.index(base)
                image[t] = options[t].index(moved)
            seen.add(tuple(image))
        yield [row for triple_set in selected for row in sorted(triple_set)]


def matchings(vertices):
    if not vertices:
        yield ()
        return
    a, *rest = vertices
    for b in rest:
        for pairs in matchings(tuple(v for v in rest if v != b)):
            yield ((a, b),) + pairs


def filter_mates(shell, contacts, shared, possible):
    mates = []
    for vertices in contacts.T:
        choices = [pairs for pairs in matchings(tuple(np.flatnonzero(vertices)))
                   if all(possible[a, b] for a, b in pairs)]
        table = np.full((len(choices), 72), -1, dtype=int)
        for k, pairs in enumerate(choices):
            for a, b in pairs:
                table[k, a], table[k, b] = b, a
        mates.append(table)
    constraints = []
    for p, q in combinations(range(27), 2):
        if shell[p, q]:
            continue
        common = np.flatnonzero(shell[p] * shell[q])
        if len(common) == 1:
            r, = common
            y, = np.flatnonzero(contacts[:,p] * contacts[:,q])
            u, = np.flatnonzero(shell[r] * shell[p])
            v, = np.flatnonzero(shell[r] * shell[q])
            left = contacts[mates[p][:,y], v]
            right = contacts[mates[q][:,y], u]
            constraints.append((p, q, (left[:,None] | right[None,:]).astype(bool)))
        if len(common) == 0:
            y, z = np.flatnonzero(contacts[:,p] * contacts[:,q])
            def possible_caps(a, b):
                first = mates[p][:,a,None]
                second = mates[q][None,:,b]
                return (first != second) & (shared[first, second] < 2)
            constraints.append((p, q, possible_caps(y, z) | possible_caps(z, y)))
    alive = [np.ones(len(table), dtype=bool) for table in mates]
    while all(a.any() for a in alive):
        before = sum(a.sum() for a in alive)
        for p, q, allowed in constraints:
            alive[p] &= allowed[:,alive[q]].any(axis=1)
            alive[q] &= allowed[alive[p]].any(axis=0)
        if before == sum(a.sum() for a in alive):
            break
    return [table[keep] for table, keep in zip(mates, alive)]


def bit_indices(bits):
    while bits:
        bit = bits & -bits
        yield bit.bit_length()-1
        bits ^= bit


def mask(indices):
    return sum(1 << int(i) for i in indices)


def exterior_rows(labels, needs, possible, shared, mates):
    uses = [mask(j for j, row in enumerate(labels) if p in row) for p in range(27)]
    conflict = [mask(np.flatnonzero(row >= 2)) for row in shared]
    domains = []
    for y, labels_y in enumerate(labels):
        need = needs[y].tolist()
        available = mask(np.flatnonzero(possible[y]))
        for p in labels_y:
            available &= ~uses[p] | mask(set(mates[p][:, y]))
        rows = []
        def visit(candidates, chosen):
            score = None
            pivot = None
            for p, k in enumerate(need):
                if k:
                    n = (candidates & uses[p]).bit_count()
                    if n < k:
                        return
                    cost = n if k == 1 else n*(n-1)//2
                    if score is None or cost < score:
                        score, pivot = cost, p
            if pivot is None:
                assert chosen.bit_count() == 11
                rows.append(chosen)
                return
            choices = candidates & uses[pivot]
            for group in combinations(bit_indices(choices), need[pivot]):
                remaining = candidates & ~choices
                selected = chosen
                feasible = True
                for v in group:
                    if conflict[v] & selected or any(need[p] == 0 for p in labels[v]):
                        feasible = False
                        break
                    selected |= 1 << v
                    remaining &= ~conflict[v]
                    for p in labels[v]:
                        need[p] -= 1
                        if need[p] == 0:
                            remaining &= ~uses[p]
                if feasible:
                    visit(remaining, selected)
                for v in bit_indices(selected ^ chosen):
                    for p in labels[v]:
                        need[p] += 1
        visit(available, 0)
        assert len(rows) == len(set(rows))
        domains.append(rows)
    return domains


def row_contradiction(domains, shared):
    # The dense products count common exterior neighbors exactly, with maximum 11.
    rows = [np.array([[bits >> j & 1 for j in range(72)] for bits in group],
                     dtype=np.int16) for group in domains]
    while all(len(group) for group in rows):
        before = sum(map(len, rows))
        for i, j in combinations(range(72), 2):
            a, b = rows[i], rows[j]
            edge = a[:,j,None]
            valid = (edge == b[:,i]) & (a@b.T + edge == 2-shared[i,j])
            rows[i], rows[j] = a[valid.any(axis=1)], b[valid.any(axis=0)]
            if not len(rows[i]) or not len(rows[j]):
                return True
        if before == sum(map(len, rows)):
            return False
    return True


def main():
    seen = set()
    counts = []
    survivors = []
    for key in product(range(6), repeat=4):
        if key in seen:
            continue
        steps = transport(key)
        actions = list(relabelings(steps))
        orbit = {k for k, _ in actions}
        assert key in orbit and not (seen & orbit)
        seen.update(orbit)
        shell = shell_matrix(steps)
        options = boundary_options(shell)
        if not all(options):
            continue
        bad = uncovered_squares(shell)
        actions = [a for k, a in actions if k == key]
        models = list(boundaries(options, actions))
        counts.append((len(orbit), len(models), bad))
        if bad:
            continue
        for labels in models:
            contacts = np.zeros((72,27), dtype=np.int16)
            contacts[np.arange(72)[:,None], labels] = 1
            assert np.array_equal(shell@shell + shell + contacts.T@contacts, 12*np.eye(27)+2)
            shared = contacts@contacts.T
            needs = 2-contacts-contacts@shell
            possible = (shared < 2) & ((needs == 0).astype(int)@contacts.T == 0)
            possible &= possible.T.copy()
            mates = filter_mates(shell, contacts, shared, possible)
            if all(len(group) for group in mates):
                assert {len(m) for m in mates} == {4}
                rows = exterior_rows(labels, needs, possible, shared, mates)
                assert Counter(map(len, rows)) == {33: 54, 312: 18}
                assert row_contradiction(rows, shared)
                survivors.append(key)
    assert len(seen) == 1296
    assert counts == [(108,2,3), (216,21,4), (54,51,4), (36,6,6), (2,6,0)]
    assert survivors == [(3,4,4,3)]
    print("1296 tables, 416 with feasible marginals, 86 boundary types.")
    print("Full coverage: 6 after shell squares, 1 after shell matchings, 0 after exterior rows.")


if __name__ == "__main__":
    main()
