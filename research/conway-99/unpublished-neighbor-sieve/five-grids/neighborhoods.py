"""Exact neighborhood and square tests for a 27-point shell and 72 contact triples."""

from functools import cache
from itertools import combinations
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from triangle_array import bit_indices, mask, matchings


@cache
def matching_patterns(size):
    return list(matchings(tuple(range(size))))


def shell_matchings(shell, contacts, possible):
    near = np.hstack((shell, contacts.T)).astype(bool)
    neighbors = [set(np.flatnonzero(row)) for row in near]
    choices = []
    for p, ns in enumerate(neighbors):
        fixed = {}
        for q in ns:
            if q < 27:
                z, = ns & neighbors[q]
                fixed[q], fixed[z] = z, q
        free = sorted(ns-set(fixed))
        assert all(y >= 27 for y in free)
        rows = []
        for pattern in matching_patterns(len(free)):
            pairs = [(free[i], free[j]) for i,j in pattern]
            if all(possible[a,b] for a,b in pairs):
                row = np.full(99, -1, dtype=int)
                for a,b in list(fixed.items())+pairs:
                    row[a], row[b] = b,a
                rows.append(row)
        if not rows:
            return []
        choices.append(np.stack(rows))
    constraints = []
    for p,q in combinations(range(27), 2):
        if shell[p,q]:
            continue
        a,b = neighbors[p] & neighbors[q]
        m,n = choices[p], choices[q]
        allowed = possible[m[:,a,None],n[None,:,b]] | possible[m[:,b,None],n[None,:,a]]
        if not allowed.any():
            return []
        if not allowed.all():
            constraints.append((p,q,allowed))
    alive = [np.ones(len(m), dtype=bool) for m in choices]
    while True:
        before = sum(a.sum() for a in alive)
        for p,q,allowed in constraints:
            alive[p] &= allowed[:,alive[q]].any(axis=1)
            alive[q] &= allowed[alive[p]].any(axis=0)
            if not alive[p].any() or not alive[q].any():
                return []
        if before == sum(a.sum() for a in alive):
            return [m[a] for m,a in zip(choices,alive)]


def exterior_rows(y, labels, needs, eligible, uses, conflict):
    need = list(map(int,needs[y]))
    def visit(available, chosen):
        best = None
        pivot = None
        for p,k in enumerate(need):
            if k:
                n = (available & uses[p]).bit_count()
                if n < k:
                    return
                cost = n if k == 1 else n*(n-1)//2
                if best is None or cost < best:
                    best, pivot = cost,p
        if pivot is None:
            assert chosen.bit_count() == 11
            yield chosen
            return
        candidates = available & uses[pivot]
        for group in combinations(bit_indices(candidates), need[pivot]):
            remaining = available & ~candidates
            selected = 0
            for v in group:
                if selected & conflict[v] or any(need[p] == 0 for p in labels[v]):
                    break
                selected |= 1 << v
                remaining &= ~conflict[v]
                for p in labels[v]:
                    need[p] -= 1
                    if need[p] == 0:
                        remaining &= ~uses[p]
            else:
                yield from visit(remaining, chosen | selected)
            for v in bit_indices(selected):
                for p in labels[v]:
                    need[p] += 1
    yield from visit(mask(np.flatnonzero(eligible[y])), 0)


def feasible_fan(y, row, shell_neighbors, edge_masks, common_cap_edges, no_shared_shell):
    # Use absolute vertex indices throughout. A matched pair completes a triangle at y.
    vertices = shell_neighbors[27+y] | (row << 27)
    mates = {}
    fixed = 0
    for p in bit_indices(shell_neighbors[27+y]):
        hits = shell_neighbors[p] & vertices
        assert hits.bit_count() == 1
        q = hits.bit_length()-1
        mates[p], mates[q] = q,p
        fixed |= (1 << p) | (1 << q)
    free = vertices & ~fixed
    allowed = {a: free & edge_masks[a] & no_shared_shell[a-27]
               for a in bit_indices(free)}
    restrictions = []
    for p in range(27):
        if p in mates:
            continue
        r,s = bit_indices(shell_neighbors[p] & vertices)
        restrictions.append((r,s,common_cap_edges[p][s],common_cap_edges[p][r]))
    def visit(left):
        for a,b,opposite_a,opposite_b in restrictions:
            if a in mates and b in mates:
                if not ((opposite_a >> mates[a] | opposite_b >> mates[b]) & 1):
                    return False
        if not left:
            return True
        a = min(bit_indices(left), key=lambda v: (left & allowed[v]).bit_count())
        for b in bit_indices(allowed[a] & left):
            mates[a],mates[b] = b,a
            if visit(left ^ (1 << a) ^ (1 << b)):
                return True
            del mates[a],mates[b]
        return False
    return visit(free)


def check_boundary(shell, labels, witness):
    labels = [tuple(map(int,row)) for row in labels]
    assert len(labels) == len(set(labels)) == 72
    contacts = np.zeros((72,27), dtype=np.int16)
    contacts[np.arange(72)[:,None],labels] = 1
    assert np.array_equal(shell@shell+shell+contacts.T@contacts, 12*np.eye(27)+2)
    shared = contacts@contacts.T
    needs = 2-contacts-contacts@shell
    eligible = (shared < 2) & ((needs == 0).astype(np.int16)@contacts.T == 0)
    eligible &= eligible.T.copy()
    possible = np.block([[shell,contacts.T],[contacts,eligible]]).astype(bool)
    matching = shell_matchings(shell, contacts, possible)
    if not matching:
        assert witness is None
        return 'shell'
    assert witness is not None
    uses = [mask(np.flatnonzero(r)) for r in contacts.T]
    conflict = [mask(np.flatnonzero(r >= 2)) for r in shared]
    shell_neighbors = [mask(np.flatnonzero(r)) for r in possible[:27]]
    shell_neighbors.extend(mask(row) for row in labels)
    edge_masks = [mask(np.flatnonzero(r)) for r in possible]
    no_shared_shell = [mask(np.flatnonzero(r == 0)) << 27 for r in shared]
    common_cap_edges = []
    for p,table in enumerate(matching):
        cap_edges = {}
        for a in bit_indices(shell_neighbors[p]):
            caps = set(table[:,a])
            reaches = 0
            for b in caps:
                reaches |= edge_masks[b]
            cap_edges[a] = reaches
            if a >= 27 and needs[a-27,p]:
                assert min(caps) >= 27
                allowed = np.zeros(72, dtype=bool)
                allowed[[b-27 for b in caps]] = True
                eligible[a-27] &= (contacts[:,p] == 0) | allowed
        common_cap_edges.append(cap_edges)
    eligible &= eligible.T.copy()
    def viable_rows(y):
        for row in exterior_rows(y, labels, needs, eligible, uses, conflict):
            if feasible_fan(y, row, shell_neighbors, edge_masks, common_cap_edges, no_shared_shell):
                yield row
    if isinstance(witness,int):
        assert next(viable_rows(witness), None) is None
        return 'exterior'
    i,j = witness
    left,right = list(viable_rows(i)),list(viable_rows(j))
    assert len(left) == len(right) == 1
    assert not any((a >> j & 1) == (b >> i & 1) and
                   (a & b).bit_count()+(a >> j & 1) == 2-shared[i,j]
                   for a in left for b in right)
    return 'pair'
