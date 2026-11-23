"""Exact counting bounds for rooted norm-18 windows and the rank-36 shell test."""

from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, product
import json
from math import ceil, comb
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from short_shell_moments import FAMILIES, SHIFTS, fmpq_mat, moment_rows


def check_triple_capacity(fours, labels, edge_count):
    # Star triples can occur once, all other triples at most twice.
    capacities = {triple: (1 if set.intersection(*(set(labels[i]) for i in triple)) else 2)
                  for triple in combinations(range(6), 3)}
    triples = [tuple(combinations(sorted(four), 3)) for four in fours]

    def extend(start, chosen):
        assert chosen + edge_count <= 6
        for index in range(start, len(triples)):
            used = triples[index]
            if all(capacities[t] for t in used):
                for t in used:
                    capacities[t] -= 1
                extend(index+1, chosen+1)
                for t in used:
                    capacities[t] += 1

    extend(0, 0)


def independent_windows():
    labels = list(combinations(range(4), 2))
    opposite = [ij for ij in combinations(range(6), 2)
                if set(labels[ij[0]]).isdisjoint(labels[ij[1]])]
    transitions = [[None, *combinations([i for i, p in enumerate(labels) if v in p], 2)]
                   for v in range(4)]
    for raw in product(*transitions):
        adjacent = [pair for pair in raw if pair is not None]
        for k in range(4):
            for cross in combinations(opposite, k):
                edges = adjacent + list(cross)
                neighbors = [set() for _ in range(11)]
                for i,j in ([(0,1+j) for j in range(4)]
                            + [(1+j,5+i) for i,p in enumerate(labels) for j in p]
                            + [(5+i,5+j) for i,j in edges]):
                    neighbors[i].add(j)
                    neighbors[j].add(i)
                if any(len(neighbors[i] & neighbors[j]) > 2-int(j in neighbors[i])
                       for i,j in combinations(range(11), 2)):
                    continue
                independent = sum(all(not set(edge) <= set(four) for edge in edges)
                                  for four in combinations(range(6), 4))
                assert 9*(15-independent) >= 5*(len(adjacent)+8*k)

                # In a family with all pairwise dot products seven, the positive
                # pair-label sets have pairwise intersections of size at most two.
                # With two or more members all sets have size four, so their
                # two-element complements are pairwise disjoint.
                fours = [set(four) for four in combinations(range(6),4)
                         if all(not set(edge) <= set(four) for edge in edges)]
                check_triple_capacity(fours, labels, len(adjacent)+k)
                cap = max((n for n in (1,2,3) if any(
                    all(len(a & b) <= 2 for a,b in combinations(group,2))
                    for group in combinations(fours,n))), default=0)
                assert 8*cap + 2*len(adjacent) + 3*k <= 24
    slots = 15*99*560 - Q(5,9)*8*99*420
    assert slots/9 == Q(215600,3)
    total_cap = Q(24*99*560 - 16*99*84 - 3*99*336 + 78*851, 8)
    assert ceil(9*16684-total_cap) == 4645
    assert total_cap == Q(582045,4) and 2*(total_cap//18) == 16166
    assert 2*((6*99*560 - 99*1008 + 42*851)//18) == 29842


def norm24_windows():
    # In a root neighborhood b disjoint mate edges forbid choosing both endpoints.
    def choose(n,k):
        return comb(n,k) if 0 <= k <= n else 0

    for k in range(4):
        for b in range((4+k)//2+1):
            n = 4+k-2*b
            def count(m):
                return sum(2**h*choose(b,h)*choose(n,m-h) for h in range(m+1))
            assert count(4) >= 1+4*k-3*b
            assert count(3) >= 4+6*k-3*b
    assert 2*12*11100-3*55440 == 100080
    assert 3*48*1776-6*27720 == 89424


def difference_windows():
    edges = list(combinations(range(4), 2))
    weights = {}
    for heights in combinations_with_replacement(range(3), 4):
        count = 0
        for omissions in combinations(edges, 2):
            extra = [sum(q in e for e in omissions)-heights[q] for q in range(4)]
            if all(value in (0, 1) for value in extra) and sum(extra) <= 2:
                count += 1
        weights[heights] = count
    max_count = 0
    for mates in combinations_with_replacement(list(combinations_with_replacement(range(3), 2)), 7):
        heights = sum(mates, ())
        if sum(heights) != 16 or heights.count(2) > 8:
            continue
        count = sum(weights[tuple(sorted(values))]
                    for selection in combinations(mates, 4) for values in product(*selection))
        max_count = max(count, max_count)
    assert max_count == 904


def population_bounds():
    moment = sum((moment_rows(shift) for shift in (*SHIFTS, None)), [])
    keys = sorted(set().union(*moment))
    reduced = fmpq_mat([[row.get(k,0) for k in keys] for row in moment]).rref()[0]
    rows = [[Q(str(v)) for v in row] for row in reduced.tolist() if any(row)]
    assert len(rows) == 7
    for target, source, multiplicity in [
        ((1,25),(0,16),8), ((1,27),(0,18),9), ((1,27),(2,26),2), ((0,26),(1,21),8),
    ]:
        for row in rows:
            row[keys.index(source)] += multiplicity*row[keys.index(target)]
    graph_bound = [Q(0)]*len(keys)
    graph_bound[keys.index((0,18))] = 1
    graph_bound[keys.index((0,16))] = -Q(11*904,18)
    injection = [Q(0)]*len(keys)
    injection[keys.index((0,16))] = 1
    injection[keys.index((1,27))] = -1
    coefficients = list(zip(*rows, graph_bound, injection))
    cert = json.loads((HERE/'population-duals.json').read_text())
    duals = [list(map(Q, row)) for row in cert['duals']]
    unit = set().union(*FAMILIES, {(2,26)})
    pairs = list(combinations(sorted(unit), 2))
    p = 2402
    for ban16, indices in enumerate(cert['indices']):
        assert len(indices) == len(pairs) == 66
        bounds = {(0,0):(1,1), (0,14):(0,4), (1,23):(99,None),
                  (0,16):(0,Q(0 if ban16 else 6930,p)), (0,18):(0,Q(289520,p))}
        minima = []
        for pair, i in zip(pairs, indices):
            y = duals[i]
            assert len(y) == len(rows)+2 and max(y[-2:]) <= 0
            lower = y[-2]*Q(215600,3*p)
            for k, col in zip(keys, coefficients):
                c = int(k in unit and k not in pair)-sum(u*v for u,v in zip(y,col))
                lo, hi = bounds.get(k, (0,None))
                if c < 0:
                    assert hi is not None
                    lower += c*hi
                else:
                    lower += c*lo
            minima.append(p*lower)
        assert min(minima) == (Q(640164,5669), Q(8407))[ban16]
        print('Rank 36, number left after deleting any two unit types:', ceil(min(minima)),
              '(no norm-16 vectors)' if ban16 else '(unconditional)')


if __name__ == '__main__':
    independent_windows()
    norm24_windows()
    difference_windows()
    population_bounds()
