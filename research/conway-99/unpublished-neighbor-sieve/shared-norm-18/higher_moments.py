"""Verify a weight-28/30/32 shell identity of the rank-48 marked neighbors."""

from collections import defaultdict
import json
from itertools import product
from math import isqrt
from pathlib import Path
import sys

from flint import fmpq_mat

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from short_shell_moments import DUAL7, FAMILIES, GRAM, SHIFTS, dot, moment_rows, possible, times


# Coordinates are unit counts after the four short-shell subtractions.
RELATION = {
    (0, 0): 31725, (0, 14): 245, (0, 16): -3372, (0, 20): 2375,
    (0, 24): 180, (0, 26): 11, (1, 21): 1769, (1, 23): -435,
    (1, 27): 290, (2, 26): -270, (2, 28): -825, (2, 30): 650,
    (2, 34): -46, (3, 35): -180, (3, 37): -11, (4, 44): -738,
}
DIRECTIONS = ((1,0,0), (0,1,0), (1,1,1), (2,1,1), (1,2,-1), (2,1,-2),
              (1,-1,1), (0,1,2), (1,0,2), (3,1,2), (1,2,3), (1,3,-1))


def projections(shift, shell):
    """Return all integral projection numerators at fixed squared norm 2*shell."""
    scale = 1 if shift is None else 3
    bounds = [isqrt(scale**2 * 2 * shell * GRAM[i][i]) for i in range(4)]
    offsets = [((0,)*4, 1)] if shift is None else [
        (tuple(j*x for x in times(GRAM, shift)), 3) for j in (-1, 0, 1)]
    table = defaultdict(list)
    for offset, step in offsets:
        entries = [range(-b + (b+r) % step, b+1, step) for b, r in zip(bounds, offset)]
        for w in product(*entries):
            h = dot(w, times(DUAL7, w))
            if h > 14*shell*scale**2:
                continue
            charges = (0, 3) if shift is None else ((-dot(shift,w)+4) % 9 - 4,)
            for a in charges:
                scaled_norm = (9 // scale**2) * h
                t, rem = divmod(126*shell - scaled_norm + 11*a*a, 9)
                if a >= 0 and rem == 0 and possible(a,t):
                    table[a,t].append(w)
    return table


def root_projections(shift):
    scale = 1 if shift is None else 3
    return [tuple(scale*x for x in GRAM[i]) for i in (0,2)
            if shift is None or dot(GRAM[i],shift) % 3 == 0]


def trace_row(shift, table):
    scale = 1 if shift is None else 3
    row = defaultdict(int)
    for (a,t), vectors in table.items():
        row[a,t] = (2 if a else 1)*sum(12*dot(w,times(DUAL7,w))-28*scale**2 for w in vectors)
    row[0,0] += 48*2*len(root_projections(shift))*22*7*scale**2
    row[0,14] -= 48*2*7*scale**2
    return row


def real_power(w, direction, degree):
    a,b,c = direction
    u,v = c*(a+4*b), -c*(2*a+b)
    x,y = (a+u)*w[0]+(b+v)*w[1], (a-u)*w[2]+(b-v)*w[3]
    re,im = 1,0
    for _ in range(degree):
        re,im = re*x-im*y, im*x+re*y
    return re


def rows():
    raw = []
    for shift in (*SHIFTS, None):
        raw.extend(moment_rows(shift))
        raw.append(trace_row(shift, projections(shift, 2)))
    shift = SHIFTS[0]
    four, six = projections(shift, 2), projections(shift, 3)
    # For weight 24+d the shell-6 sum is c1 times the root sum plus c2 times shell 4.
    for degree, c1, c2 in [(4,151740,192), (6,-99180,-552), (8,50220,432)]:
        for direction in DIRECTIONS:
            row = defaultdict(int)
            row[0,0] = -2*c1*sum(real_power(w,direction,degree) for w in root_projections(shift))
            for table, factor in ((six,1), (four,-c2)):
                for (a,t), vectors in table.items():
                    row[a,t] += factor*(2 if a else 1)*sum(real_power(w,direction,degree) for w in vectors)
            raw.append(row)
    for row in raw:
        for target,source,mult in [((1,25),(0,16),8), ((1,27),(0,18),9),
                                   ((1,27),(2,26),2), ((0,26),(1,21),8)]:
            row[source] = row.get(source,0) + mult*row.get(target,0)
    return raw


def main():
    equations = rows()
    keys = sorted(set(RELATION).union(*equations))
    matrix = [[r.get(k,0) for k in keys] for r in equations]
    rank = fmpq_mat(matrix).rank()
    assert fmpq_mat(matrix+[[RELATION.get(k,0) for k in keys]]).rank() == rank
    ten = set().union(*FAMILIES,{(2,26)}) - {(0,18),(1,25)}
    slack = {k:2375*int(k in ten)-RELATION.get(k,0) for k in keys}
    assert all(value >= 0 for k,value in slack.items() if k not in ((0,0),(0,14)))
    assert slack[0,0] + 4*slack[0,14] + 99*slack[1,23] == 10360
    # If exactly the norm-18 and norm-24 types occur, the other ten columns vanish.
    unit = set().union(*FAMILIES,{(2,26)})
    keep = [k for k in keys if k not in unit-{(0,18),(0,24)}]
    restricted = [[r.get(k,0) for k in keep] for r in equations]
    rank = fmpq_mat(restricted).rank()
    for identity in [
        {(0,18):6, (0,0):-93, (0,14):-2, (1,23):-2, (2,22):-5},
        {(0,24):6, (0,0):-45, (0,14):-1, (1,23):-13, (2,22):-34, (3,35):-6},
    ]:
        assert fmpq_mat(restricted+[[identity.get(k,0) for k in keep]]).rank() == rank

    models = json.loads((HERE/'population-examples.json').read_text())
    for graph_rank in (36,38,40,42):
        model = models['36' if graph_rank == 36 else '38-42']
        populations = {tuple(k):v for k,v in model}
        assert len(populations) == len(model) and set(populations) <= set(keys)
        assert all(type(v) is int and v > 0 for v in populations.values())
        assert all(sum(row.get(k,0)*v for k,v in populations.items()) == 0 for row in equations)
        assert populations[0,0] == 1 and populations.get((0,14),0) <= 4 and populations[1,23] >= 99
        p = 7**((44-graph_rank)//2) + 1
        bound = 12320 if graph_rank == 42 else 16166
        assert (populations[0,18]*p > bound) == (graph_rank == 38)
        present = unit & set(populations)
        assert present == ({(0,18),(0,24),(0,26)} if graph_rank == 36 else {(0,18),(0,24)})
    print('Certified lower bound after removing (0,18) and (1,25): 2072/475 per extension.')


if __name__ == '__main__':
    main()
