#!/usr/bin/env python3
"""Exact finite checks for geometry-next.md; not a universal proof."""

from fractions import Fraction as F
from math import factorial
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def product(values):
    ans = F(1)
    for value in values:
        ans *= value
    return ans


def evaluate(weights, t, blocks):
    d = len(weights)
    require(d >= 3, "dimension")
    require(F(0) < t <= min(weights), "simplex cap hypothesis")
    require(max(weights) == 1, "weight normalization")
    S = sum(weights)
    A = product(weights)
    c = t ** (d - 1) / (factorial(d - 1) * A)
    V = F(2 ** d) - 2 * t ** d / (factorial(d) * A)
    H = S - t
    alpha = [F(2 ** (d - 1)) - c * w for w in weights]
    require(min(alpha) > 0 and V > 0 and H > 0, "positivity")
    require(2 * sum(alpha) + 2 * c * H == d * V,
            "complete facet cone normalization")
    lifted_hP = (2 * sum(alpha) + 2 * c * S) / (d * V)
    v = 2 * t ** d / (d * factorial(d - 1) * A * V)
    require(lifted_hP - 1 == v, "support surplus")
    total_norm_sq = sum(w * w for w in weights)
    max_block_sq = max(sum(weights[i] ** 2 for i in block) for block in blocks)
    dist_sq = total_norm_sq - max_block_sq
    require(dist_sq > 0, "at least one coordinate outside every block")
    new_cone_mass = 2 * c * H / (d * V)
    sample_dist_sq = dist_sq / H ** 2
    s_sq = 4 * c ** 2 * dist_sq / (d ** 2 * V ** 2)
    require(new_cone_mass ** 2 * sample_dist_sq == s_sq,
            "squared mean-distance formula")
    require(A ** 2 <= dist_sq, "restricted geometry lower bound")
    require(s_sq >= (t ** (d - 1) / (factorial(d) * 2 ** (d - 1))) ** 2,
            "dimension-dependent normal-distance lower bound")
    lam = H / S
    require(1 - lam == t / S, "homothetic containment")
    require(F(0) < lam <= 1, "containment range")
    if t <= F(1, 2):
        require(1 / lam - 1 <= 2 * t, "Banach-Mazur upper bound")
    return {"V": V, "v": v, "s_sq": s_sq, "tau": t / S}


cases = 0
near_axis_cases = 0
for d in range(3, 13):
    lines = [(i,) for i in range(d)]
    planes = [tuple(range(i, min(i + 2, d))) for i in range(0, d, 2)]
    for denominator in (2, 3, 5, 11):
        eps = F(1, denominator)
        for weights in ([F(1)] * d,
                        [F(1)] + [eps] * (d - 1),
                        [F(1)] + [F(1, denominator + i) for i in range(1, d)]):
            for factor in (1, 2):
                t = min(weights) / factor
                for blocks in (lines, planes):
                    evaluate(weights, t, blocks)
                    cases += 1
        near = evaluate([F(1)] + [eps] * (d - 1), eps, lines)
        expected_v = 2 * eps / (d * factorial(d - 1) * near["V"])
        require(near["v"] == expected_v, "near-axis surplus")
        require(near["s_sq"] == (d - 1) * expected_v ** 2,
                "near-axis normal distance")
        ratio_sq = near["v"] ** 2 / (near["tau"] ** 2 * near["s_sq"])
        require(ratio_sq == (1 + (d - 1) * eps) ** 2 / ((d - 1) * eps ** 2),
                "failure of extra containment-error factor")
        near_axis_cases += 1

print(json.dumps({
    "status": "PASS",
    "weighted_corner_cut_cases": cases,
    "near_axis_counterexample_cases": near_axis_cases,
    "total_cases": cases + near_axis_cases,
    "arithmetic": "exact rational; squared normal distances",
    "scope": "finite identities only; analytic proofs are in geometry-next.md"
}, sort_keys=True))
