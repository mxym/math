"""Exact certificate replay for a fully covered point on no rook grid. Requires NumPy."""

from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
import gzip
import json
from pathlib import Path

import numpy as np


PAIRS = [(i,j) for j in range(7) for i in range(j)]


def encode(edges):
    return sum((1 if (i,j) in edges else 2) << (2*k) for k,(i,j) in enumerate(PAIRS))


def tournament_codes():
    for scores in combinations_with_replacement((0,2,3,4), 7):
        if sum(scores) != 21:
            continue
        groups = [tuple(i for i,s in enumerate(scores) if s == k) for k in sorted(set(scores))]
        symmetries = list(product(*(permutations(group) for group in groups)))
        seen = set()

        def complete(i, indegrees, edges):
            if i == 7:
                yield edges
                return
            remaining = scores[i] - indegrees[i]
            if 0 <= remaining <= 6-i:
                for inward in combinations(range(i+1,7), remaining):
                    new_degrees = indegrees.copy()
                    new_edges = edges.copy()
                    for j in range(i+1,7):
                        if j in inward:
                            new_edges.add((j,i))
                        else:
                            new_degrees[j] += 1
                            new_edges.add((i,j))
                    if all(x <= s for x,s in zip(new_degrees,scores)):
                        yield from complete(i+1, new_degrees, new_edges)

        for edges in complete(0, [0]*7, set()):
            code = encode(edges)
            if code in seen:
                continue
            yield code
            for parts in symmetries:
                perm = sum(parts, ())
                seen.add(encode({(perm[a],perm[b]) for a,b in edges}))


def flow_basis(edges):
    matrix = np.array([[int(e[role] == axis) for e in edges]
                       for role in (0,1) for axis in range(7)], dtype=np.int64)
    pivot = []
    for col in range(len(edges)):
        r = len(pivot)
        hits = np.flatnonzero(matrix[r:,col])
        if not len(hits):
            continue
        i = r + hits[0]
        matrix[[r,i]] = matrix[[i,r]]
        assert abs(matrix[r,col]) == 1
        matrix[r] *= matrix[r,col]
        factors = matrix[:,col].copy()
        factors[r] = 0
        matrix -= factors[:,None]*matrix[r]
        pivot.append(col)
    free = [j for j in range(len(edges)) if j not in pivot]
    basis = np.zeros((len(edges),len(free)), dtype=np.int64)
    basis[free] = np.eye(len(free), dtype=np.int64)
    basis[pivot] = -matrix[:len(pivot),free]
    return basis, free


def row_system(edges):
    basis, free = flow_basis(edges)
    candidates = np.array(list(product((-1,0,1), repeat=len(free)))) @ basis.T
    candidates = candidates[np.max(abs(candidates), axis=1) <= 1]
    by_cell = []
    cells = edges + [pair for pair in combinations(range(7),2)
                     if pair not in edges and pair[::-1] not in edges]
    for i,(a,b) in enumerate(cells):
        dirty = i < len(edges)
        keep = candidates[:,i] == -1 if dirty else np.ones(len(candidates), dtype=bool)
        for j,(c,d) in enumerate(edges):
            if i == j:
                continue
            if dirty and (a == c or b == d):
                keep &= candidates[:,j] >= 0
            elif a in (c,d) or b in (c,d):
                keep &= candidates[:,j] == 0
        by_cell.append(candidates[keep])
    rows = np.concatenate(by_cell)
    owner = np.repeat(np.arange(len(cells)), list(map(len,by_cell)))
    indicator = np.eye(len(cells), dtype=np.int64)[:,owner]
    matrix = list(indicator)
    rhs = [4]*len(cells)
    for i in range(len(cells)):
        coeff = indicator[i]
        if i < len(edges):
            coeff = coeff - basis[i] @ indicator[free]
        for j in free:
            entry = coeff * rows[:,j]
            if np.any(entry):
                matrix.append(entry)
                rhs.append(0)
    for i in free:
        for j in free:
            matrix.append((rows[:,i] + 7*indicator[i]) * rows[:,j])
            rhs.append(0)
    return np.array(matrix), np.array(rhs), owner, rows


def check_leaf(matrix, rhs, owner, weights):
    if len(set(owner)) < 21:
        assert not weights
        return
    assert weights and len({i for i,value in weights}) == len(weights)
    u = np.zeros(len(rhs), dtype=np.int64)
    for i, value in weights:
        assert 0 <= i < len(rhs) and 0 < abs(value) <= 10000
        u[i] = value
    # Entries have magnitude at most eight, and fewer than 1,000 rows are used.
    assert len(u) < 1000 and np.max(abs(matrix)) <= 8
    assert np.max(u @ matrix) <= 0 and u @ rhs > 0


def verify_permutations(system, group, weights_by_factor, require_two_cycle=False, omit=None):
    matrix, rhs, owner, rows = system
    pairs = list(combinations(group,2))
    factors = set()
    for seq in permutations(group):
        perm = dict(zip(group,seq))
        if all(perm[i] != i for i in group):
            factors.add(tuple(int(perm[i] == j) + int(perm[j] == i) for i,j in pairs))
    if require_two_cycle:
        factors = {factor for factor in factors if 2 in factor}
    if omit is not None:
        factors.remove(omit)
    assert len(factors) == len(weights_by_factor)
    extra = np.array([(owner == i)*rows[:,j] for i,j in pairs])
    matrix = np.vstack((matrix,extra))
    for factor, weights in zip(sorted(factors), weights_by_factor):
        keep = np.ones(len(owner), dtype=bool)
        for (i,j),v in zip(pairs,factor):
            if v != 1:
                keep &= ~(((owner == i) & (rows[:,j] != v//2))
                          | ((owner == j) & (rows[:,i] != v//2)))
        target = np.r_[rhs, 2*np.array(factor)]
        check_leaf(matrix[:,keep],target,owner[keep],weights)
    return len(factors)


def verify(code, certificate):
    edges = [(i,j) if ((code >> (2*k)) & 3) == 1 else (j,i)
             for k,(i,j) in enumerate(PAIRS)]
    system = row_system(edges)
    if isinstance(certificate, list):
        check_leaf(*system[:3],certificate)
        return 1
    groups = [[i for i,(a,b) in enumerate(edges) if a == axis] for axis in range(7)]
    group, = (g for g in groups if len(g) == 6)
    return verify_permutations(system,group,certificate['tails'])


if __name__ == '__main__':
    with gzip.open(Path(__file__).with_name('covered-spread-cert.json.gz'), 'rt') as f:
        certificates = {int(k):v for k,v in json.load(f).items()}
    census = Counter()
    for code in tournament_codes():
        census[verify(code,certificates.pop(code))] += 1
    assert not certificates and census == {1:94,130:2}
    print("Verified 96 tournaments and 354 impossibility certificates.")
