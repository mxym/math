#!/usr/bin/env python3
"""Exact finite normalized-cover verifier. Standard-library Python only.

Input JSON:
  {"points": ["1/8", "1/4"], "holes": [["1/10", "1"]],
   "max_density": "9/10"}
H is the union of these OPEN intervals and all their integer translates.
Check: for every 0 <= x <= 1 and 1 <= t <= 2, some x+t*a belongs to H.

This verifies a supplied finite certificate, not the similarity theorem or
existence of any uncomputed small-density blocker. Exponential worst-case
runtime. Boundary-only failures are retained and reported exactly.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from pathlib import Path
from typing import Iterable
import json
import sys

Point = tuple[Q, Q]
Interval = tuple[Q, Q]


def rational(v: object) -> Q:
    if isinstance(v, bool) or not isinstance(v, (int, str)):
        raise ValueError("Rationals must be integer or string, never floating point")
    return Q(v)


def floor_q(v: Q) -> int:
    return v.numerator // v.denominator


def ceil_q(v: Q) -> int:
    return -((-v.numerator) // v.denominator)


def merged_open_translates(holes: list[Interval], lo: Q, hi: Q) -> list[Interval]:
    intervals = []
    for a, b in holes:
        if a >= b:
            raise ValueError("Every hole must have strictly increasing endpoints")
        # Include boundary-touching translates: their endpoints remain outside H.
        for m in range(ceil_q(lo-b), floor_q(hi-a)+1):
            intervals.append((a+m, b+m))
    intervals.sort()
    result: list[Interval] = []
    for a, b in intervals:
        if result and a < result[-1][1]:
            result[-1] = (result[-1][0], max(b, result[-1][1]))
        else:
            result.append((a, b))
    return result


def gaps(holes: list[Interval], lo: Q, hi: Q) -> list[Interval]:
    intervals = merged_open_translates(holes, lo, hi)
    if not intervals:
        return [(lo, hi)]
    raw = [(lo, intervals[0][0])]
    raw += [(intervals[i][1], intervals[i+1][0]) for i in range(len(intervals)-1)]
    raw.append((intervals[-1][1], hi))
    answer = []
    for a, b in raw:
        a, b = max(a, lo), min(b, hi)
        if a <= b:
            answer.append((a, b))
    return answer


def density(holes: list[Interval]) -> Q:
    total = Q(0)
    for a, b in merged_open_translates(holes, Q(0), Q(1)):
        total += max(Q(0), min(Q(1), b)-max(Q(0), a))
    return total


def clip(poly: tuple[Point, ...], a: Q, b: Q, c: Q) -> tuple[Point, ...]:
    """Intersect a closed convex polygon (possibly a segment/point) with ax+bt<=c."""
    if not poly:
        return ()
    result = []
    prev = poly[-1]
    vp = a*prev[0] + b*prev[1] - c
    for current in poly:
        vc = a*current[0] + b*current[1] - c
        if (vp <= 0) != (vc <= 0):
            s = vp / (vp-vc)
            result.append((prev[0]+s*(current[0]-prev[0]), prev[1]+s*(current[1]-prev[1])))
        if vc <= 0:
            result.append(current)
        prev, vp = current, vc
    unique = []
    seen = set()
    for p in result:
        if p not in seen:
            unique.append(p)
            seen.add(p)
    return tuple(unique)


def inside_periodic_open(z: Q, holes: list[Interval]) -> bool:
    for a, b in holes:
        # Strict inequalities z-b < m < z-a for an integer translate m.
        if floor_q(z-b)+1 <= ceil_q(z-a)-1:
            return True
    return False


def check(data: dict) -> dict:
    points = sorted(set(rational(a) for a in data["points"]))
    if not points:
        raise ValueError("At least one rational representative is required")
    holes = [(rational(row[0]), rational(row[1])) for row in data["holes"]]
    rho = density(holes)
    budget = rational(data.get("max_density", "1"))
    if budget < 0 or budget > 1:
        raise ValueError("Require 0 <= max_density <= 1")
    if rho > budget:
        return {"valid": False, "reason": "measure budget exceeded", "density": str(rho)}
    lo = min(Q(0), min(min(a, 2*a) for a in points))
    hi = max(Q(1), max(Q(1)+max(a, 2*a) for a in points))
    complement = gaps(holes, lo, hi)
    rectangle = ((Q(0), Q(1)), (Q(1), Q(1)), (Q(1), Q(2)), (Q(0), Q(2)))
    stack = [(0, rectangle)]
    visited = 0
    while stack:
        j, poly = stack.pop()
        visited += 1
        if j == len(points):
            x, t = poly[0]
            # Validate the returned witness independently of the gap routine.
            if not all(not inside_periodic_open(x+t*a, holes) for a in points):
                raise ArithmeticError("Internal error: invalid uncovered witness")
            return {"valid": False, "reason": "uncovered parameter pair", "density": str(rho),
                    "witness": {"x": str(x), "t": str(t)}, "states_visited": visited}
        for left, right in complement:
            reduced = clip(poly, Q(1), points[j], right)
            reduced = clip(reduced, Q(-1), -points[j], -left)
            if reduced:
                stack.append((j+1, reduced))
    return {"valid": True, "density": str(rho), "states_visited": visited,
            "claim": "all x in [0,1], all t in [1,2], some listed point hits the periodic open holes"}


def self_test() -> list[dict]:
    cases = [
        ("true normalized toy cover", {"points": ["1/8", "1/4"], "holes": [["1/10", "1"]], "max_density": "9/10"}, True),
        ("boundary-only obstruction", {"points": ["1/8", "1/4"], "holes": [["1/8", "1"]]}, False),
        ("empty blocker", {"points": ["1/8"], "holes": []}, False),
        ("whole circle", {"points": ["1/8"], "holes": [["-1/10", "11/10"]]}, True),
        ("touching open intervals leave singletons", {"points": ["1/8", "3/8"], "holes": [["0", "1/2"], ["1/2", "1"]]}, False),
        ("density budget enforced", {"points": ["1/8", "1/4"], "holes": [["1/10", "1"]], "max_density": "1/2"}, False),
    ]
    answers = []
    for name, data, expected in cases:
        answer = check(data)
        if answer["valid"] is not expected:
            raise ArithmeticError(f"Regression failed: {name}: {answer}")
        answers.append({"name": name, **answer})
    return answers


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("certificate", type=Path, nargs="?")
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    if args.self_test:
        print(json.dumps({"status": "PASS", "tests": self_test()}, indent=2))
    elif args.certificate:
        answer = check(json.loads(args.certificate.read_text(encoding="utf-8")))
        print(json.dumps(answer, indent=2))
        if not answer["valid"]:
            sys.exit(1)
    else:
        p.error("Provide a certificate or --self-test")


if __name__ == "__main__":
    main()
