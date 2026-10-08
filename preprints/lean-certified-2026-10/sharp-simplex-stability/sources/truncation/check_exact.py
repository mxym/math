#!/usr/bin/env python3
"""Exact regressions for the written all-dimensional truncation proof.

No numerical fit or convex hull solver is used. Run normally and with -O.
The rational 3D hull volume reconstructs the difference body from vertices,
independently of the orthant-integration argument in proof.tex.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import factorial
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def det(rows):
    a = [list(map(F, row)) for row in rows]
    n = len(a)
    answer = F(1)
    for i in range(n):
        pivot = next((j for j in range(i, n) if a[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            answer = -answer
        value = a[i][i]
        answer *= value
        for j in range(i + 1, n):
            scale = a[j][i] / value
            if scale:
                for k in range(i + 1, n):
                    a[j][k] -= scale * a[i][k]
    return answer


def leibniz_det(rows):
    n = len(rows)
    answer = F(0)
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        term = F(-1 if inversions % 2 else 1)
        for i in range(n):
            term *= rows[i][perm[i]]
        answer += term
    return answer


def cols_det(cols):
    return det(list(zip(*cols)))


def solve(matrix, rhs):
    n = len(matrix)
    a = [list(map(F, row)) + [F(value)] for row, value in zip(matrix, rhs)]
    for i in range(n):
        pivot = next((j for j in range(i, n) if a[j][i]), None)
        require(pivot is not None, "singular barycentric matrix")
        a[i], a[pivot] = a[pivot], a[i]
        scale = a[i][i]
        a[i] = [x / scale for x in a[i]]
        for j in range(n):
            if j != i:
                scale = a[j][i]
                a[j] = [x - scale * y for x, y in zip(a[j], a[i])]
    return [row[-1] for row in a]


def unit_vectors(d):
    return [tuple(F(i == j) for j in range(d)) for i in range(d)]


def vertices(d, t):
    top = unit_vectors(d)
    return top + [tuple(t * x for x in v) for v in top]


def invariant_from_facets(d, t, counts):
    c = F(1, factorial(d - 1))
    q, r = t ** (d - 1), 1 - t ** (d - 1)
    normals = [tuple(-c * r * x for x in e) for e in unit_vectors(d)]
    normals += [(c,) * d, (-c * q,) * d]
    supports = [F(0)] * d + [c, -c * t ** d]
    lifted = [u + (b,) for u, b in zip(normals, supports)]
    horizontal = F(0)
    for indices in combinations(range(d + 2), d):
        rows = list(zip(*(normals[i] for i in indices)))
        value = det(rows)
        horizontal += abs(value)
        counts['horizontal_minors'] += 1
        if d <= 3:
            require(value == leibniz_det(rows), "horizontal determinant implementations disagree")
            counts['leibniz_crosschecks'] += 1
    lift_sum = F(0)
    for indices in combinations(range(d + 2), d + 1):
        rows = list(zip(*(lifted[i] for i in indices)))
        value = det(rows)
        lift_sum += abs(value)
        counts['lifted_minors'] += 1
        if d <= 3:
            require(value == leibniz_det(rows), "lifted determinant implementations disagree")
            counts['leibniz_crosschecks'] += 1
    expected_h = c ** d * r ** (d - 1) * (d + 1 + (d - 1) * q)
    expected_l = c ** (d + 1) * r ** (d - 1) * (1 + (d - 1) * q - (d - 1) * t ** d - q * t ** d)
    require(horizontal == expected_h, "horizontal sum mismatch")
    require(lift_sum == expected_l, "lifted sum mismatch")
    volume = (1 - t ** d) / factorial(d)
    a = lift_sum / (d * volume * horizontal)
    expected_a = (1 + (d - 1) * q - (d - 1) * t ** d - q * t ** d) / ((1 - t ** d) * (d + 1 + (d - 1) * q))
    defect = a - F(1, d + 1)
    expected_defect = t ** (d - 1) * (d * (d - 1) - (d + 1) * (d - 2) * t - 2 * t ** d) / ((d + 1) * (1 - t ** d) * (d + 1 + (d - 1) * q))
    require(a == expected_a and defect == expected_defect > 0, "invariant/defect formula mismatch")
    if d == 3:
        require(defect == t * t * (t * t + t + 3) / (4 * (1 + t + t * t) * (2 + t * t)), "tetrahedral cancellation mismatch")
    return {'d': d, 't': t, 'volume': volume, 'horizontal_sum': horizontal,
            'lifted_sum': lift_sum, 'a': a, 'defect': defect,
            'leading_coefficient': F(d * (d - 1), (d + 1) ** 2)}


def maximum_vertex_simplex_checks(d, t, counts):
    pts = vertices(d, t)
    best = F(0)
    maximizers = []
    for indices in combinations(range(2 * d), d + 1):
        value = abs(cols_det([pts[i] + (F(1),) for i in indices]))
        counts['vertex_simplex_subsets'] += 1
        rays = [i % d for i in indices]
        if len(set(rays)) < d:
            expected = F(0)
        else:
            bottom = sum(i >= d for i in indices)
            expected = (1 - t) * t ** (bottom - 1)
        require(value == expected, "vertex simplex determinant mismatch")
        if value > best:
            best, maximizers = value, [indices]
        elif value == best:
            maximizers.append(indices)
    require(best == 1 - t, "wrong maximum simplex volume")
    expected_maximizers = [tuple(list(range(d)) + [d + i]) for i in range(d)]
    require(maximizers == expected_maximizers, "wrong maximizing vertex configurations")
    return {'d': d, 't': t, 'maximum_volume': best / factorial(d),
            'vertex_maximizers': maximizers}


def barycentric_checks(d, t, counts):
    pts = vertices(d, t)
    p_lists = [unit_vectors(d)[0], (F(1, d),) * d,
               tuple(F(i + 1, d * (d + 1) // 2) for i in range(d)),
               tuple([F(1, 2), F(1, 2)] + [F(0)] * (d - 2))]
    results = []
    for p in p_lists:
        simplex = [tuple(t * x for x in p)] + unit_vectors(d)
        matrix = list(zip(*(v + (F(1),) for v in simplex)))
        require(abs(det(matrix)) == 1 - t, "maximum nonvertex simplex volume mismatch")
        coords = [solve(matrix, x + (F(1),)) for x in pts]
        for x, beta in zip(pts, coords):
            b0 = (1 - sum(x)) / (1 - t)
            formula = [b0] + [x[i] - t * p[i] * b0 for i in range(d)]
            require(beta == formula, "barycentric coordinate mismatch")
            counts['barycentric_vertex_checks'] += 1
        minima = [min(beta[i] for beta in coords) for i in range(d + 1)]
        require(minima == [F(0)] + [-t * pi for pi in p], "barycentric extrema mismatch")
        excess = -(d + 1) * min(minima)
        require(excess == (d + 1) * t * max(p), "centroid excess mismatch")
        require(1 - sum(minima) == 1 + t, "translated homothet factor mismatch")
        # Exact volume consistency for the unrestricted BM upper factor.
        require((1 + t) ** d >= sum(t ** i for i in range(d)), "BM volume bracket inconsistent")
        results.append({'d': d, 't': t, 'p': p, 'barycentric_minima': minima,
                        'centroid_excess': excess, 'translated_factor': 1 + t})
    return results


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def hull2_projected(points, dropped):
    axes = [i for i in range(3) if i != dropped]
    pts = sorted((tuple(p[i] for i in axes), p) for p in points)

    def turn(a, b, c):
        aa, bb, cc = a[0], b[0], c[0]
        return (bb[0] - aa[0]) * (cc[1] - aa[1]) - (bb[1] - aa[1]) * (cc[0] - aa[0])

    lower, upper = [], []
    for point in pts:
        while len(lower) >= 2 and turn(lower[-2], lower[-1], point) <= 0:
            lower.pop()
        lower.append(point)
    for point in reversed(pts):
        while len(upper) >= 2 and turn(upper[-2], upper[-1], point) <= 0:
            upper.pop()
        upper.append(point)
    return [p for _, p in lower[:-1] + upper[:-1]]


def rational_hull_volume3(points, counts):
    """Every supporting facet is found by triples; 2D hulls remove interior points."""
    pts = sorted(set(points))
    faces = {}
    checked_planes = set()
    for a, b, c in combinations(pts, 3):
        normal = cross(subtract(b, a), subtract(c, a))
        if not any(normal):
            continue
        offset = dot(normal, a)
        divisor = next(x for x in normal if x)
        key = tuple(x / divisor for x in normal) + (offset / divisor,)
        if key in checked_planes:
            continue
        checked_planes.add(key)
        signs = [dot(normal, p) - offset for p in pts]
        if any(x > 0 for x in signs) and any(x < 0 for x in signs):
            continue
        face = tuple(p for p, value in zip(pts, signs) if value == 0)
        faces[face] = normal
    volume = F(0)
    triangles = []
    for face, normal in sorted(faces.items()):
        dropped = next(i for i, x in enumerate(normal) if x)
        polygon = hull2_projected(face, dropped)
        require(len(polygon) >= 3, "degenerate supporting facet")
        for i in range(1, len(polygon) - 1):
            triangle = [polygon[0], polygon[i], polygon[i + 1]]
            six_volume = abs(cols_det(triangle))
            require(six_volume > 0, "origin not strictly inside difference body")
            volume += six_volume / 6
            triangles.append({'vertices': triangle, 'six_volume': six_volume})
    counts['difference_body_supporting_facets'] += len(faces)
    counts['difference_body_boundary_triangles'] += len(triangles)
    return volume, len(pts), len(faces), triangles


def difference_body_checks(t, counts):
    pts = vertices(3, t)
    differences = [subtract(a, b) for a, b in product(pts, repeat=2)]
    volume, point_count, face_count, triangles = rational_hull_volume3(differences, counts)
    expected = (10 - 3 * t - 6 * t * t - t ** 3) / 3
    require(volume == expected, "independent difference body volume mismatch")
    k_volume = (1 - t ** 3) / 6
    deficit = 1 - volume / (20 * k_volume)
    require(deficit == 3 * t * (1 + 3 * t) / (10 * (1 + t + t * t)), "RS deficit mismatch")
    return {'d': 3, 't': t, 'difference_body_volume': volume,
            'rogers_shephard_deficit': deficit, 'point_count': point_count,
            'facet_count': face_count, 'boundary_triangles': triangles}


def main():
    counts = {'horizontal_minors': 0, 'lifted_minors': 0,
              'leibniz_crosschecks': 0, 'vertex_simplex_subsets': 0,
              'barycentric_vertex_checks': 0,
              'difference_body_supporting_facets': 0,
              'difference_body_boundary_triangles': 0}
    grid = [F(1, 100), F(1, 10), F(1, 3), F(1, 2), F(9, 10)]
    facet_records, vertex_records, barycentric_records = [], [], []
    for d in range(2, 10):
        for t in grid:
            facet_records.append(invariant_from_facets(d, t, counts))
            barycentric_records.extend(barycentric_checks(d, t, counts))
            if d <= 6:
                vertex_records.append(maximum_vertex_simplex_checks(d, t, counts))
            # Independently check all inequalities used to attain s(K_t)=d-t.
            r = F(d) - t
            z = F(1) / (r + 1)
            require((r + 1) * z == 1, "asymmetry coordinate inequality")
            require(1 + r * t <= (r + 1) * d * z == r + t, "asymmetry sum inequalities")
    difference_records = [difference_body_checks(t, counts) for t in grid]
    output = {'status': 'all exact checks passed', 'counts': counts,
              'facet_records': facet_records, 'maximum_vertex_records': vertex_records,
              'barycentric_records': barycentric_records,
              'difference_body_records': difference_records,
              'scope': 'Finite exact regressions; the infinite-dimensional-index family and exponent limits are proved in proof.tex.'}
    path = Path(__file__).resolve().with_name('exact_certificate.json')
    path.write_text(json.dumps(output, indent=2, default=str) + '\n')
    print('All exact rational checks passed.')
    print(json.dumps(counts, sort_keys=True))
    print('Facet/geometry grid: d=2..9; vertex-subset enumeration: d=2..6.')
    print('Parameters: 1/100, 1/10, 1/3, 1/2, 9/10.')
    print('Dimension-three difference-body volumes independently reconstructed from rational supporting facets.')
    print('Certificate: exact_certificate.json')


if __name__ == '__main__':
    main()
