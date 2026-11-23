"""Exact rank-36 population certificates for exactly three unit types."""

from fractions import Fraction
from itertools import combinations
import json
from math import ceil, gcd, lcm
from pathlib import Path

from flint import fmpq_mat
from higher_moments import FAMILIES, SHIFTS, moment_rows, rows


UNIT = set().union(*FAMILIES, {(2,26)})
P = 2402


def short_equations():
    short = sorted(set().union({(2,34)}, *(set(r) for shift in (*SHIFTS,None) for r in moment_rows(shift))))
    original = rows()
    other = sorted(set().union(*original)-set(short))
    order = other+short
    reduced, rank = fmpq_mat([[r.get(k,0) for k in order] for r in original]).rref()
    equations = []
    for row in reduced.tolist()[:rank]:
        if any(row[:len(other)]):
            continue
        coeffs = [Fraction(str(x)) for x in row[len(other):]]
        denominator = lcm(*(x.denominator for x in coeffs))
        integer = [int(denominator*x) for x in coeffs]
        common = gcd(*integer)
        equations.append([x//common for x in integer])
    assert len(short) == 24 and len(equations) == 9
    return short, equations


def system(keys, equations, allowed):
    keep = [i for i,k in enumerate(keys) if k not in UNIT-allowed]
    active = [keys[i] for i in keep]
    matrix = [[row[i] for i in keep] for row in equations]
    rhs = [0]*len(matrix)

    def append(weights, target):
        matrix.append([weights.get(k,0) for k in active])
        rhs.append(target)

    append({(0,0):1}, 1)
    first_upper = len(matrix)
    append({(1,23):-1}, -99)
    append({(0,14):1}, 4)
    append({(0,16):P}, 6930)
    if not {(0,16),(0,20)} & allowed:
        append({(0,18):P}, 16166)
    append({(0,18):9*P,(0,16):-4972*P}, 646800)
    append({(0,16):1,(1,27):-1}, 0)
    for i,row in enumerate(matrix):
        row.extend(int(i == j) for j in range(first_upper,len(matrix)))
    return active, matrix, rhs


def dot(u,v):
    assert len(u) == len(v)
    return sum(a*b for a,b in zip(u,v))


def main():
    keys, rows = short_equations()
    proof = json.loads(Path(__file__).with_name('rank36-three-type-duals.json').read_text())
    triples = set(combinations(sorted(UNIT),3))
    for raw, y in proof['infeasible']:
        triple = tuple(map(tuple,raw))
        triples.remove(triple)
        _, matrix, target = system(keys, rows, set(triple))
        assert dot(target,y) < 0 and all(dot(col,y) >= 0 for col in zip(*matrix))
    assert len(triples) == 10
    assert [t for t in triples if (0,18) in t] == [((0,18),(0,24),(0,26))]
    assert all((0,16) not in t for t in triples)
    feasible = set()
    for raw, denominator, sparse in proof['feasible']:
        triple = tuple(map(tuple,raw))
        active, matrix, target = system(keys, rows, set(triple))
        x = [0]*len(matrix[0])
        assert denominator > 0
        for i,v in sparse:
            assert 0 <= i < len(x) and not x[i] and v > 0
            x[i] = v
        assert all(x[active.index(k)] > 0 for k in triple)
        assert all(dot(row,x) == denominator*b for row,b in zip(matrix,target))
        feasible.add(triple)
    assert feasible == triples
    branch_minima = {(0,26):[], (3,37):[]}
    for raw, key, denominator, y in proof['branch_bounds']:
        triple, key = tuple(map(tuple,raw)), tuple(key)
        triples.remove(triple)
        assert {key} == set(triple) & branch_minima.keys() and denominator > 0
        active, matrix, target = system(keys, rows, set(triple))
        assert all(dot(col,y) <= (P*denominator if i == active.index(key) else 0)
                   for i,col in enumerate(zip(*matrix)))
        branch_minima[key].append(ceil(Fraction(dot(target,y),denominator)))
    assert not triples
    assert {k:(len(v),min(v)) for k,v in branch_minima.items()} == {
        (0,26):(8,807072), (3,37):(2,288984)}
    active, matrix, target = system(keys, rows, {(0,18),(0,24),(0,26)})
    bounds = {}
    for k, bound, denominator, y in proof['lower_bounds']:
        k = tuple(k)
        assert denominator > 0 and dot(target,y) == denominator*bound
        assert all(dot(col,y) <= (P*denominator if i == active.index(k) else 0)
                   for i,col in enumerate(zip(*matrix)))
        bounds[k] = bound
    assert bounds == {(0,18):8407,(0,24):252210,(0,26):1389116}
    print('Rank 36: 210 of 220 triples excluded. Bounds for the unique triple with norm 18:', bounds)


if __name__ == '__main__':
    main()
