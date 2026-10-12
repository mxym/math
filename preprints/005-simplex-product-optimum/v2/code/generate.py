#!/usr/bin/env python3
"""Produce rational proof data; no floating point and no external dependencies.

The analytic identities and the infinite-parameter arguments are in paper.md.
This producer is NOT the independent verifier; run check.py on its output.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import json
from math import factorial
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


@lru_cache(None)
def g(n: int) -> F:
    if n < 0:
        raise ValueError("negative dimension")
    return F(n ** n, factorial(n)) if n else F(1)


def simplex(n: int) -> F:
    return (n + 1) * g(n)


@dataclass(frozen=True)
class State:
    R: F
    V: F  # V = a R; this is NOT the volume of the convex body.
    recipe: dict


def upper_hull(points: list[State]) -> list[State]:
    """Vertices of the positive-normal upper convex hull, exactly."""
    points.sort(key=lambda p: (p.R, p.V))
    unique: list[State] = []
    for p in points:
        if unique and p.R == unique[-1].R:
            unique[-1] = p
        else:
            unique.append(p)
    pareto: list[State] = []
    best_v = F(-1)
    for p in reversed(unique):
        if p.V > best_v:
            pareto.append(p)
            best_v = p.V
    hull: list[State] = []
    for p in reversed(pareto):
        while len(hull) >= 2:
            a, b = hull[-2:]
            cross = ((b.R - a.R) * (p.V - a.V)
                     - (b.V - a.V) * (p.R - a.R))
            if cross >= 0:
                hull.pop()
            else:
                break
        hull.append(p)
    return hull


def finite_closure(limit: int = 14) -> list[list[State]]:
    levels = [[State(F(1), F(1), {"op": "point"})]]
    for n in range(1, limit + 1):
        candidates: list[State] = []
        for r in range(1, n // 2 + 1):
            s = n - r
            for i, a in enumerate(levels[r]):
                for j, b in enumerate(levels[s]):
                    candidates.append(State(
                        a.R * b.R,
                        (r * a.V * b.R + s * a.R * b.V) / n,
                        {"op": "product", "left": [r, i], "right": [s, j]}))
        for r in range((n - 1) // 2 + 1):
            s = n - 1 - r
            coeff = g(n) / (g(r) * g(s))
            for i, a in enumerate(levels[r]):
                for j, b in enumerate(levels[s]):
                    candidates.append(State(
                        coeff * (a.R * b.V + a.V * b.R),
                        coeff * a.V * b.V,
                        {"op": "join", "left": [r, i], "right": [s, j]}))
        levels.append(upper_hull(candidates))
    return levels


def recursive_family(last_level: int = 6) -> list[dict]:
    """K0=T5; K(j+1)=(Kj x Kj)*(Kj x Kj)."""
    n, value, alpha = 5, simplex(5), F(1, 6)
    data = []
    for j in range(last_level + 1):
        data.append({"level": j, "dimension": n,
                     "R": str(value), "a": str(alpha)})
        if j < last_level:
            new_n = 4 * n + 1
            value = value ** 4 * g(new_n) / g(2 * n) ** 2 * (2 * alpha)
            n, alpha = new_n, alpha / 2
    return data


def generate() -> dict:
    levels = finite_closure()
    family = recursive_family()
    n = family[-1]["dimension"]
    value = F(family[-1]["R"])
    lo, hi = F(14267, 5000), F(5707, 2000)
    # Analytic proof: (3 R_j^3)^(1/(3d_j+1)) < Lambda
    #                  < (6 R_j^3)^(1/(3d_j+1)).
    if not lo ** (3 * n + 1) < 3 * value ** 3:
        raise ArithmeticError("lower endpoint is not certified")
    if not 6 * value ** 3 < hi ** (3 * n + 1):
        raise ArithmeticError("upper endpoint is not certified")
    for k in range(1, 14):
        if max(s.R for s in levels[k]) != simplex(k):
            raise ArithmeticError(f"unexpected small-dimensional optimum: {k}")
    if max(s.R for s in levels[14]) != F(385, 384) * simplex(14):
        raise ArithmeticError("unexpected dimension-fourteen optimum")
    root_upper = F(561993, 200000)  # 2.809965
    if not simplex(13) < root_upper ** 13:
        raise ArithmeticError("old asymptotic root upper bound failed")
    if not lo > F(203, 200) * root_upper:
        raise ArithmeticError("exponential comparison failed")
    return {
        "schema": "mxym-math-005-join-calculus-v2-exact-1",
        "scope": "Finite rational evidence; paper.md supplies geometric and infinite proofs.",
        "finite_closure": {
            "limit": 14,
            "coordinates": ["R", "a*R"],
            "levels": [[{"R": str(s.R), "V": str(s.V), "recipe": s.recipe}
                        for s in level] for level in levels],
            "optimal_to_simplex_ratios": [
                str(max(s.R for s in levels[k]) / simplex(k))
                for k in range(1, 15)]},
        "recursive_family": {
            "definition": "K0=T5; K(j+1)=(Kj x Kj)*(Kj x Kj)",
            "levels": family,
            "limit_lower": str(lo), "limit_upper": str(hi),
            "tail_factor_lower": "3", "tail_factor_upper": "6",
            "comparison_level": 6, "comparison_exponent": 3 * n + 1},
        "old_product_class_comparison": {
            "root_upper": str(root_upper),
            "eventual_exponential_factor": "203/200"},
        "explicit_pyramid_witness": {
            "definition": "Pyramid^6(T4 x T4)", "dimension": 14,
            "ratio_to_simplex": "385/384", "a": "1/11"}
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "certificates/exact.json")
    args = parser.parse_args()
    data = generate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    sizes = [len(x) for x in data["finite_closure"]["levels"]]
    print("Produced exact upper-hull certificate, dimensions 0..14:", sizes)
    print("Produced exact self-similar values through level 6, dimension 21845.")
    print("Certified arithmetic endpoints: 2.8534 < Lambda < 2.8535.")
    print("Next run the separate check.py; a producer pass is not independent verification.")


if __name__ == "__main__":
    main()
