#!/usr/bin/env python3
"""Independent permutation-determinant regressions, with no producer imports."""
from fractions import Fraction as F
from itertools import permutations, product, combinations
from math import factorial
from functools import lru_cache


def require(ok, description):
    if not ok:
        raise RuntimeError(description)


def determinant(rows):
    n = len(rows)
    result = F(0)
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        value = F((-1) ** inversions)
        for i in range(n):
            value *= rows[i][p[i]]
        result += value
    return result


def positive(x):
    return max(F(0), x)


def witness(a, b):
    return min(positive(a), positive(-b)) + min(positive(-a), positive(b))


counts = {"barycentric_points": 0, "first_identities": 0,
          "exact_pair_identities": 0, "cancellation_bases": 0,
          "lifted_moment_tuples": 0, "singular_bases": 0}

for d in (1, 2, 3):
    zero = (F(0),) * d
    anchors = [zero] + [tuple(F(i == j, 2) for j in range(d)) for i in range(d)]
    signed_v = determinant([p + (F(1),) for p in anchors])
    v = abs(signed_v)
    for coordinates in product((F(-1), F(-1, 2), F(0), F(1, 2), F(1)), repeat=d):
        alpha = (1 - sum(coordinates),) + coordinates
        x = tuple(coordinates[i] / 2 for i in range(d))
        require(sum(t*t for t in x) <= 1, "test point not in ball")
        for i in range(d + 1):
            base = [anchors[k] for k in range(d + 1) if k != i]
            a = determinant([p + (F(1),) for p in base + [anchors[i]]])
            c = determinant([p + (F(1),) for p in base + [x]])
            require(witness(a, c) == v * min(F(1), positive(-alpha[i])),
                    "first witness identity failed")
            counts["first_identities"] += 1
        for i, j in combinations(range(d + 1), 2):
            base = [x] + [anchors[k] for k in range(d + 1) if k not in (i, j)]
            a = determinant([p + (F(1),) for p in base + [anchors[i]]])
            c = determinant([p + (F(1),) for p in base + [anchors[j]]])
            expected = v * (min(positive(alpha[i]), positive(alpha[j]))
                            + min(positive(-alpha[i]), positive(-alpha[j])))
            require(witness(a, c) == expected, "full pair witness identity failed")
            counts["exact_pair_identities"] += 1
        r = max(range(d + 1), key=lambda i: alpha[i])
        nx = sum(positive(-a) for a in alpha)
        ux = sum(positive(alpha[i]) for i in range(d + 1) if i != r)
        difference = [x[k] - anchors[r][k] for k in range(d)]
        require(sum(t*t for t in difference) <= 4 * (nx + ux)**2,
                "assignment distance bound failed")
        require(ux <= sum(min(positive(alpha[i]), positive(alpha[j]))
                          for i, j in combinations(range(d + 1), 2)),
                "positive remainder bound failed")
        counts["barycentric_points"] += 1

    # A large atom at zero deliberately produces fully zero and singular bases.
    points = [zero]
    points += [tuple(F(i == j) for j in range(d)) for i in range(d)]
    points += [tuple(-x for x in p) for p in points[1:]]
    probabilities = [F(1, 3)] + [F(1, 3*d)] * (2*d)
    require(sum(probabilities) == 1, "invalid law")
    require(all(sum(m*p[j] for m, p in zip(probabilities, points)) == 0
                for j in range(d)), "uncentered law")

    def mass(indices):
        value = F(1)
        for i in indices:
            value *= probabilities[i]
        return value

    @lru_cache(None)
    def lifted(indices):
        return determinant([points[i] + (F(1),) for i in indices])

    a_total = F(0)
    cancellation = F(0)
    psi_total = F(0)
    for base in product(range(len(points)), repeat=d):
        horizontal = determinant([points[i] for i in base])
        a_total += mass(base) * abs(horizontal)
        values = [lifted(base + (i,)) for i in range(len(points))]
        require(sum(m*f for m, f in zip(probabilities, values)) == horizontal,
                "conditional centering identity failed")
        p = sum(m * positive(f) for m, f in zip(probabilities, values))
        n = sum(m * positive(-f) for m, f in zip(probabilities, values))
        conditional = sum(probabilities[i]*probabilities[j]*witness(values[i], values[j])
                          for i in range(len(points)) for j in range(len(points)))
        require(conditional <= 2*min(p, n), "conditional witness estimate failed")
        cancellation += mass(base) * 2*min(p, n)
        psi_total += mass(base) * conditional
        counts["cancellation_bases"] += 1
        if horizontal == 0:
            counts["singular_bases"] += 1

    b_total = F(0)
    second_moment = F(0)
    for indices in product(range(len(points)), repeat=d + 1):
        value = lifted(indices)
        b_total += mass(indices) * abs(value)
        second_moment += mass(indices) * value * value
        counts["lifted_moment_tuples"] += 1
    require(b_total - a_total == cancellation, "integrated cancellation failed")
    require(psi_total <= b_total - a_total, "integrated two-sample estimate failed")
    require(second_moment == factorial(d + 1) * F(2, 3*d)**d,
            "independent affine determinant moment failed")

print("Independent exact permutation-determinant checks passed.")
print(counts)
