#!/usr/bin/env python3
"""Exact one-point extension of an acute set. Read JSON array of points on stdin."""
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
import json
import sys


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def minus(a, b):
    return tuple(x - y for x, y in zip(a, b))


def reduced(rows, d):
    rows = [list(map(F, row)) for row in rows]
    j, pivots = 0, []
    for k in range(d):
        i = next((i for i in range(j, len(rows)) if rows[i][k]), None)
        if i is None:
            continue
        rows[i], rows[j] = rows[j], rows[i]
        c = rows[j][k]
        rows[j] = [x / c for x in rows[j]]
        for i in range(len(rows)):
            if i != j and rows[i][k]:
                c = rows[i][k]
                rows[i] = [a - c * b for a, b in zip(rows[i], rows[j])]
        pivots.append(k)
        j += 1
    return rows, pivots


def initial(A, d):
    """Return independent anchored strips (or a normal to the affine span)."""
    chosen = []
    for a in A[1:]:
        if len(reduced(chosen + [a], d)[1]) > len(chosen):
            chosen.append(a)
        if len(chosen) == d:
            return chosen, None
    rows, piv = reduced(chosen, d)
    k = next(i for i in range(d) if i not in piv)
    u = [F(0)] * d
    u[k] = F(1)
    for r, p in enumerate(piv):
        u[p] = -rows[r][k]
    return None, u


def clipping(vertices, rows):
    """Clip by exact halfspaces, maintaining all vertices with tight-row masks."""
    for k, (normal, rhs) in enumerate(rows):
        bit = 1 << k
        residuals = {p: dot(normal, p) - rhs for p in vertices}
        stay = [(p, mask, residuals[p]) for p, mask in vertices.items()
                if residuals[p] < 0]
        die = [(p, mask, residuals[p]) for p, mask in vertices.items()
               if residuals[p] > 0]
        new = {p: mask | (bit if residuals[p] == 0 else 0)
               for p, mask in vertices.items() if residuals[p] <= 0}

        # A pair spans an edge iff just those two old vertices satisfy
        # all their common tight inequalities. This also handles degeneracies.
        masks = list(vertices.values())
        cached = {}
        for p, Mp, a in stay:
            for q, Mq, b in die:
                c = Mp & Mq
                if c not in cached:
                    count = 0
                    for M in masks:
                        if M & c == c:
                            count += 1
                            if count > 2:
                                break
                    cached[c] = (count == 2)
                if cached[c]:
                    r = tuple((b * pi - a * qi) / (b - a)
                              for pi, qi in zip(p, q))
                    new[r] = c | bit
        vertices = new
    return vertices


def decide(points):
    if not isinstance(points, list) or len(points) < 2 or not isinstance(points[0], list):
        raise ValueError('give at least two points as a JSON array of vectors')
    d = len(points[0])
    if d < 1 or any(not isinstance(p, list) or len(p) != d for p in points):
        raise ValueError('vectors must have the same positive dimension')
    A = [tuple(map(F, a)) for a in points]
    if len(set(A)) != len(A):
        raise ValueError('points must be distinct')
    for y in A:
        for x, z in combinations([x for x in A if x != y], 2):
            if dot(minus(x, y), minus(z, y)) <= 0:
                raise ValueError('input set itself is not acute')
    origin = A[0]
    A = [minus(a, origin) for a in A]
    scale = lcm(*(x.denominator for a in A for x in a))
    A = [tuple(int(scale * x) for x in a) for a in A]
    centroid = tuple(F(sum(a[i] for a in A), len(A)) for i in range(d))
    pairs = list(combinations(A, 2))

    def slack(x):
        return min(dot(minus(x, a), minus(x, b)) for a, b in pairs)

    def witness(x):
        assert slack(x) > 0
        assert all(dot(minus(x, a), minus(b, a)) > 0 and
                   dot(minus(x, b), minus(a, b)) > 0 for a, b in pairs)
        return dict(extendable=True, point=[str(v / scale + a) for v,a in zip(x,origin)])

    strips, normal = initial(A, d)
    if normal is not None:
        t = 1
        while True:
            X = tuple(x + t * v for x, v in zip(centroid, normal))
            if slack(X) > 0:
                return witness(X)
            t *= 2

    # Seed parallelepiped: strip directions anchored at the first point.
    h = [dot(w, w) for w in strips]
    inv, _ = reduced([list(row) + [int(i == j) for j in range(d)]
                      for i, row in enumerate(strips)], d)
    inv = [row[d:] for row in inv]
    abs_coord_bound = [sum(abs(z) * b for z, b in zip(row, h)) for row in inv]
    box_z = 1 + max(sum(abs(x+y)*M for x,y,M in zip(a,b,abs_coord_bound))
                    + abs(dot(a,b)) for a,b in pairs)
    vertices = {}
    for signs in product((0, 1), repeat=d+1):
        X = tuple(sum(t*z*b for t,z,b in zip(signs, row, h)) for row in inv)
        z = box_z if signs[-1] else -box_z
        mask = sum(1 << (2*i+s) for i,s in enumerate(signs))
        vertices[X+(z,)] = mask

    rows = []
    for a, b in pairs:
        w = minus(b, a)
        rows.extend(((w+(0,), dot(w,b)),
                     (tuple(-z for z in w)+(0,), -dot(w,a))))
    for a, b in pairs:
        rows.append((tuple(x+y for x,y in zip(a,b))+(-1,),dot(a,b)))
    # Leave the original tight-row IDs intact; the clipping rows begin at bit
    # 2(d+1), even when the same geometric inequality is inserted again.
    start = 2*(d+1)
    vertices = clipping(vertices, [(tuple([0]*(d+1)),1)]*start + rows)
    best = max(vertices, key=lambda xz: dot(xz[:-1],xz[:-1]) - xz[-1])
    x, z = best[:-1], best[-1]
    mx = dot(x,x)-z
    if mx <= 0:
        return dict(extendable=False, maximum_squared_slack=str(mx/(scale**2)),
                    epigraph_vertices=len(vertices))
    t = F(1,2)
    while True:
        X = tuple((1-t)*a + t*b for a,b in zip(x,centroid))
        if slack(X) > 0:
            return witness(X)
        t /= 2


if __name__ == '__main__':
    try:
        obj = json.load(sys.stdin, parse_float=F)
        print(json.dumps(decide(obj), indent=2))
    except (ValueError, TypeError, ZeroDivisionError) as exc:
        print(f'acute-extend: {exc}', file=sys.stderr)
        sys.exit(2)
