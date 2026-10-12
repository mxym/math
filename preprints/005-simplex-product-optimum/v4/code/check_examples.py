#!/usr/bin/env python3
from fractions import Fraction
from itertools import product

Q = Fraction

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def det(mat):
    n = len(mat)
    if n == 0:
        return Q(1)
    if n == 1:
        return mat[0][0]
    total = Q(0)
    for j, a in enumerate(mat[0]):
        if a:
            minor = [row[:j] + row[j+1:] for row in mat[1:]]
            total += (-1 if j & 1 else 1) * a * det(minor)
    return total

def columns_det(cols):
    n = len(cols)
    require(all(len(c) == n for c in cols), "determinant is not square")
    mat = [[cols[j][i] for j in range(n)] for i in range(n)]
    return det(mat)

def expectations(points, weights):
    d = len(points[0])
    require(len(points) == len(weights), "weight count mismatch")
    require(sum(weights, Q(0)) == 1, "weights do not sum to one")
    require(all(len(p) == d for p in points), "point dimension mismatch")
    mean = [sum((weights[k] * points[k][i] for k in range(len(points))), Q(0))
            for i in range(d)]
    require(mean == [Q(0)] * d, "law is not centered")

    A = Q(0)
    for idx in product(range(len(points)), repeat=d):
        prob = Q(1)
        cols = []
        for k in idx:
            prob *= weights[k]
            cols.append(points[k])
        A += prob * abs(columns_det(cols))

    B = Q(0)
    for idx in product(range(len(points)), repeat=d+1):
        prob = Q(1)
        cols = []
        for k in idx:
            prob *= weights[k]
            cols.append(points[k] + (Q(1),))
        B += prob * abs(columns_det(cols))
    return A, B

def rademacher_expectation(coeffs):
    coeffs = [Q(c) for c in coeffs]
    total = Q(0)
    for eps in product((-1, 1), repeat=len(coeffs)):
        total += abs(sum((eps[i] * coeffs[i] for i in range(len(coeffs))), Q(0)))
    return total / (2 ** len(coeffs))

def weak_compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in weak_compositions(total - first, parts - 1):
            yield (first,) + rest

def check_rademacher_grid():
    checked = 0
    for m in range(2, 7):
        for denominator in range(2, 11):
            for numerators in weak_compositions(denominator, m):
                if max(numerators) * 2 > denominator:
                    continue
                coeffs = [Q(n, denominator) for n in numerators]
                value = rademacher_expectation(coeffs)
                support = sum(n != 0 for n in numerators)
                predicted = support <= 3 or max(numerators) * 2 == denominator
                require(value <= Q(1,2), f"Rademacher upper bound failed: {numerators}")
                require((value == Q(1,2)) == predicted,
                        f"Rademacher equality classification failed: {numerators}, value={value}")
                checked += 1
    return checked

def uniform_signed(vectors):
    pts = []
    for v in vectors:
        v = tuple(Q(x) for x in v)
        pts.extend([v, tuple(-x for x in v)])
    return pts, [Q(1, len(pts))] * len(pts)

def cube_vertices(d):
    pts = [tuple(Q(x) for x in eps) for eps in product((-1, 1), repeat=d)]
    return pts, [Q(1, len(pts))] * len(pts)

def check():
    grid_count = check_rademacher_grid()

    require(rademacher_expectation([Q(1,4)] * 4) == Q(3,8),
            "four-quarter strict benchmark failed")
    require(rademacher_expectation([Q(1,2), Q(1,6), Q(1,6), Q(1,6)]) == Q(1,2),
            "half-mass equality benchmark failed")
    require(rademacher_expectation([Q(1,3)] * 3) == Q(1,2),
            "three-term equality benchmark failed")

    q = (Q(1,3), Q(1,3), Q(1,3))
    require(sum(abs(x) for x in q) == 1, "q is not on the l1 boundary")
    pts, weights = uniform_signed([(1,0,0), (0,1,0), (0,0,1), q])
    A, B = expectations(pts, weights)
    require(A == Q(3,16), f"unexpected A for nonextreme boundary law: {A}")
    require(B == Q(3,8), f"unexpected B for nonextreme boundary law: {B}")
    require(B / (4*A) == Q(1,2), "nonextreme boundary law is not an equality case")

    axes, axes_w = uniform_signed([(1,0,0), (0,1,0), (0,0,1)])
    A_axes, B_axes = expectations(axes, axes_w)
    require(A_axes == Q(2,9), f"unexpected axes A: {A_axes}")
    require(B_axes == Q(4,9), f"unexpected axes B: {B_axes}")
    require(B_axes / (4*A_axes) == Q(1,2), "axes law is not an equality case")

    cube, cube_w = cube_vertices(3)
    A_cube, B_cube = expectations(cube, cube_w)
    require(A_cube == Q(3,2), f"unexpected cube A: {A_cube}")
    require(B_cube == Q(45,16), f"unexpected cube B: {B_cube}")
    require(B_cube / (4*A_cube) == Q(15,32), "cube strict benchmark failed")

    print("PASS: exact symmetric-equality regressions")
    print("rademacher_grid_cases =", grid_count)
    print("rademacher_four_quarters =", rademacher_expectation([Q(1,4)] * 4))
    print("half_mass_boundary_case =", rademacher_expectation([Q(1,2), Q(1,6), Q(1,6), Q(1,6)]))
    print("nonextreme_boundary_law: A =", A, "B =", B, "a =", B/(4*A))
    print("axes_boundary_d3: A =", A_axes, "B =", B_axes, "a =", B_axes/(4*A_axes))
    print("cube_vertices_boundary_d3: A =", A_cube, "B =", B_cube, "a =", B_cube/(4*A_cube))
    print("arithmetic: Fraction only; no floating point")
    print("checks remain active under python -O")

if __name__ == "__main__":
    check()
