#!/usr/bin/env python3
"""Exact regressions for matching.md; finite checks are not theorem proofs."""

import itertools
import json
import math
import random
from fractions import Fraction as F


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def det(columns):
    n = len(columns)
    matrix = [[F(columns[j][i]) for j in range(n)] for i in range(n)]
    result = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if matrix[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            result = -result
        diagonal = matrix[j][j]
        result *= diagonal
        for i in range(j + 1, n):
            ratio = matrix[i][j] / diagonal
            for k in range(j + 1, n):
                matrix[i][k] -= ratio * matrix[j][k]
            matrix[i][j] = F(0)
    return result


def cofactors(columns):
    return [
        abs(det(columns[:j] + columns[j + 1:]))
        for j in range(len(columns))
    ]


def fourth(values):
    return sorted(values, reverse=True)[3]


def axes(d):
    return [tuple(F(i == j) for i in range(d)) for j in range(d)]


def truncate(vector):
    order = sorted(range(len(vector)), key=lambda i: (-abs(vector[i]), i))
    chosen = set(order[:2])
    truncated = tuple(value if i in chosen else F(0)
                      for i, value in enumerate(vector))
    return truncated, abs(vector[order[2]])


def section_formula(alpha, beta, j, D):
    return [D * abs(alpha[j]), D * abs(beta[j])] + [
        D * abs(alpha[i] * beta[j] - alpha[j] * beta[i])
        for i in range(len(alpha)) if i != j
    ]


def apply_diagonal(vector, D):
    return (D * vector[0],) + tuple(vector[1:])


def run():
    rng = random.Random(20261007)
    cofactor_cases = 0
    truncation_cases = 0
    adjacent_edge_cases = 0
    obstruction_cases = 0
    for d in range(3, 9):
        for _ in range(150):
            D = F(1, rng.choice((1, 2, 4, 8)))
            R = 1 / D
            alpha = tuple(R * F(rng.randrange(-8, 9), 8)
                          for _ in range(d))
            beta = tuple(R * F(rng.randrange(-8, 9), 8)
                         for _ in range(d))
            j = rng.randrange(d)
            basis = [apply_diagonal(e, D) for e in axes(d)]
            columns = (basis[:j] + basis[j + 1:]
                       + [apply_diagonal(alpha, D), apply_diagonal(beta, D)])
            actual = cofactors(columns)
            expected = section_formula(alpha, beta, j, D)
            require(sorted(actual) == sorted(expected),
                    "omitted-basis cofactor formula failed")
            cofactor_cases += 1
            alpha2, s3a = truncate(alpha)
            beta2, s3b = truncate(beta)
            truncated = section_formula(alpha2, beta2, j, D)
            require(abs(fourth(expected) - fourth(truncated))
                    <= 2 * (s3a + s3b),
                    "fourth-cofactor truncation bound failed")
            truncation_cases += 1
        for _ in range(100):
            D = F(1, rng.choice((1, 2, 4, 8)))
            R = 1 / D
            i, j, k = rng.sample(range(d), 3)
            alpha = [F(0)] * d
            beta = [F(0)] * d
            for vector, selected in ((alpha, (i, j)), (beta, (j, k))):
                for position in selected:
                    vector[position] = R * F(rng.randrange(1, 9), 8)
                    if rng.randrange(2):
                        vector[position] = -vector[position]
            ra = min(abs(alpha[i]), abs(alpha[j]))
            rb = min(abs(beta[j]), abs(beta[k]))
            require(fourth(section_formula(alpha, beta, j, D))
                    >= D * D * ra * rb,
                    "adjacent-edge weighted cofactor lower bound failed")
            adjacent_edge_cases += 1
    for d in range(3, 11):
        base = axes(d)
        v12 = tuple((base[0][i] + base[1][i]) / 2 for i in range(d))
        v23 = tuple((base[1][i] + base[2][i]) / 2 for i in range(d))
        directions = base + [v12, v23]
        witness = [base[0]] + base[2:] + [v12, v23]
        require(fourth(cofactors(witness)) == F(1, 4),
                "rational sharpness witness is not 1/4")
        for denominator_factor in (1, 2, 5, 10):
            p = F(1, denominator_factor * (d + 2))
            w = (1 - 2 * p) / d
            weights = [w] * d + [p, p]
            expectation = F(0)
            for indices in itertools.combinations(range(d + 2), d + 1):
                columns = [directions[i] for i in indices]
                product = math.prod(weights[i] for i in indices)
                expectation += math.factorial(d + 1) * product * fourth(
                    cofactors(columns))
            expected = F(math.factorial(d + 1), 4) * w ** (d - 1) * p * p
            require(expectation == expected,
                    "exact rational obstruction expectation failed")
            require(w >= p, "sharpness weights are not all at least p")
            require(math.factorial(d) * w ** d
                    >= F(math.factorial(d), (d + 2) ** d),
                    "sharpness determinant lower bound failed")
            # Repetition gives at most two nonzero cofactors at full rank.
            repeated = base + [base[rng.randrange(d)]]
            require(sum(bool(c) for c in cofactors(repeated)) <= 2,
                    "repeated-direction relation support failed")
            obstruction_cases += 1
    result = {
        "status": "PASS",
        "arithmetic": "exact rational",
        "cofactor_formula_cases": cofactor_cases,
        "truncation_bound_cases": truncation_cases,
        "adjacent_edge_bound_cases": adjacent_edge_cases,
        "obstruction_formula_cases": obstruction_cases,
        "total_cases": cofactor_cases + truncation_cases
                       + adjacent_edge_cases + obstruction_cases,
        "scope": "finite algebraic regressions; not a proof of integral gates",
    }
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    run()
