#!/usr/bin/env python3
"""Independently check 005/v2 exact data, without importing generate.py.

Three checks are distinct:
  1. Downward-convex-hull closure proves the finite recursive-class bound.
  2. Integer determinants of explicit facet data check geometry numerically
     in EXACT arithmetic, including the dimension-14 witness.
  3. A central-binomial recurrence checks the self-similar values and the
     rational endpoints, using the analytic tail bounds in paper.md.
These checks do not constitute a formalization of the analytic proofs.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from fractions import Fraction
from itertools import combinations, product as cartesian_product
import json
from math import comb, factorial, lcm
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
Q = Fraction
ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def simplex_value(d: int) -> Q:
    return Q((d + 1) * d ** d, factorial(d))


def join_coefficient(r: int, s: int) -> Q:
    n = r + s + 1
    return Q(n ** n * factorial(r) * factorial(s),
             factorial(n) * (r ** r if r else 1) * (s ** s if s else 1))


def combine(op: str, r: int, x: tuple[Q, Q],
            s: int, y: tuple[Q, Q]) -> tuple[Q, Q]:
    if op == "product":
        require(r > 0 and s > 0, "point products are excluded from the grammar")
        return x[0] * y[0], (r * x[1] * y[0] + s * x[0] * y[1]) / (r + s)
    require(op == "join", "unknown operation")
    c = join_coefficient(r, s)
    return c * (x[0] * y[1] + x[1] * y[0]), c * x[1] * y[1]


def inside_downward_hull(p: tuple[Q, Q], vertices: list[tuple[Q, Q]]) -> bool:
    x, y = p
    if x < 0 or y < 0 or x > vertices[-1][0] or y > vertices[0][1]:
        return False
    for a, b in zip(vertices, vertices[1:]):
        if (y - a[1]) * (b[0] - a[0]) > (b[1] - a[1]) * (x - a[0]):
            return False
    return True


def check_finite(data: dict) -> dict:
    cert = data["finite_closure"]
    require(cert["limit"] == 14 and len(cert["levels"]) == 15, "wrong finite range")
    levels: list[list[tuple[Q, Q]]] = []
    closure_tests = 0
    for n, raw in enumerate(cert["levels"]):
        require(bool(raw), "empty hull")
        vertices = [(Q(v["R"]), Q(v["V"])) for v in raw]
        for i, p in enumerate(vertices):
            require(p[0] > 0 and p[1] > 0, "nonpositive state")
            if i:
                require(vertices[i-1][0] < p[0] and vertices[i-1][1] > p[1],
                        "hull order is not strictly increasing/decreasing")
            if i >= 2:
                a, b = vertices[i-2], vertices[i-1]
                cross = ((b[0]-a[0])*(p[1]-a[1])
                         - (b[1]-a[1])*(p[0]-a[0]))
                require(cross < 0, "upper hull is not concave")
            rec = raw[i]["recipe"]
            if n == 0:
                require(len(raw) == 1 and rec == {"op": "point"} and p == (Q(1), Q(1)),
                        "invalid initial point")
            else:
                r, j = rec["left"]
                s, k = rec["right"]
                require(0 <= r < n and 0 <= s < n, "nondecreasing recipe dimension")
                require(0 <= j < len(levels[r]) and 0 <= k < len(levels[s]), "bad recipe index")
                require(n == r + s + (rec["op"] == "join"), "recipe dimension mismatch")
                expected = combine(rec["op"], r, levels[r][j], s, levels[s][k])
                require(p == expected, "vertex is not achieved by its recipe")
        levels.append(vertices)
        if n == 0:
            continue
        # Check all ordered splits, rather than the producer's symmetry reduction.
        for r in range(1, n):
            s = n-r
            for a in levels[r]:
                for b in levels[s]:
                    require(inside_downward_hull(combine("product", r, a, s, b), vertices),
                            f"product closure failed in dimension {n}")
                    closure_tests += 1
        for r in range(n):
            s = n-1-r
            for a in levels[r]:
                for b in levels[s]:
                    require(inside_downward_hull(combine("join", r, a, s, b), vertices),
                            f"join closure failed in dimension {n}")
                    closure_tests += 1
        expected = simplex_value(n) * (Q(385, 384) if n == 14 else 1)
        require(vertices[-1][0] == expected, f"wrong sharp value in dimension {n}")
        require(Q(cert["optimal_to_simplex_ratios"][n-1]) == expected/simplex_value(n),
                "incorrect recorded optimum ratio")
    return {"dimensions": 14, "hull_vertices": sum(map(len, levels)),
            "ordered_operation_closure_tests": closure_tests,
            "optimum_ratio_at_14": "385/384"}


def integer_determinant(rows: list[list[int]]) -> int:
    """Fraction-free Bareiss elimination, checking every exact division."""
    n = len(rows)
    require(all(len(row) == n for row in rows), "nonsquare determinant")
    if not n:
        return 1
    a = [row[:] for row in rows]
    previous, sign = 1, 1
    for k in range(n-1):
        pivot_row = next((j for j in range(k, n) if a[j][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = pivot*a[i][j] - a[i][k]*a[k][j]
                quotient, remainder = divmod(numerator, previous)
                require(remainder == 0, "Bareiss division was not exact")
                a[i][j] = quotient
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def zonotope_volume(vectors: list[tuple[Q, ...]], dimension: int) -> tuple[Q, int]:
    denominator = lcm(*(v.denominator for row in vectors for v in row))
    integral = [[int(x*denominator) for x in row] for row in vectors]
    require(all(len(row) == dimension for row in integral), "wrong generator dimension")
    total, count = 0, 0
    for subset in combinations(integral, dimension):
        total += abs(integer_determinant(list(subset)))
        count += 1
    return Q(total, denominator**dimension), count


# A polytope is (dimension, volume, [(area_normal, support_numerator), ...]).
# The normals are rational vectors, not normalized Euclidean unit normals.
def simplex_facets(d: int) -> tuple:
    scale = Q(1, factorial(d-1))
    normals = [(tuple(-scale if i == j else Q(0) for i in range(d)), Q(0))
               for j in range(d)]
    normals.append((tuple(scale for _ in range(d)), scale))
    return d, Q(1, factorial(d)), normals


def product_facets(A: tuple, B: tuple) -> tuple:
    r, v, fa = A
    s, w, fb = B
    out = [(tuple(w*x for x in u)+(Q(0),)*s, w*h) for u, h in fa]
    out += [((Q(0),)*r+tuple(v*x for x in u), v*h) for u, h in fb]
    return r+s, v*w, out


def pyramid_facets(A: tuple) -> tuple:
    d, v, facets = A
    out = [((Q(0),)*d+(-v,), Q(0))]
    out += [(tuple(x/d for x in u)+(h/d,), h/d) for u, h in facets]
    return d+1, v/(d+1), out


def join_facets(A: tuple, B: tuple) -> tuple:
    r, v, fa = A
    s, w, fb = B
    n = r+s+1
    left = Q(factorial(r-1)*factorial(s), factorial(r+s))*w
    right = Q(factorial(r)*factorial(s-1), factorial(r+s))*v
    facets = [(tuple(left*x for x in u)+(Q(0),)*s+(left*h,), left*h) for u, h in fa]
    facets += [((Q(0),)*r+tuple(right*x for x in u)+(-right*h,), Q(0)) for u, h in fb]
    volume = Q(factorial(r)*factorial(s), factorial(n))*v*w
    return n, volume, facets


def measure(A: tuple) -> tuple[Q, Q, dict]:
    d, v, facets = A
    require(v > 0, "nonpositive geometric volume")
    require(all(sum(u[j] for u, _ in facets) == 0 for j in range(d)), "unbalanced facet normals")
    require(sum(h for _, h in facets) == d*v, "cone-volume identity failed")
    horizontal, hp = zonotope_volume([u for u, _ in facets], d)
    lifted, sp = zonotope_volume([u+(h,) for u, h in facets], d+1)
    require(horizontal > 0 and lifted > 0, "degenerate zonotope")
    R = horizontal/v**(d-1)
    alpha = lifted/(d*v*horizontal)
    report = {"dimension": d, "facets": len(facets), "body_volume": str(v),
              "projection_volume": str(horizontal), "lifted_volume": str(lifted),
              "horizontal_minors": hp, "lifted_minors": sp,
              "R": str(R), "a": str(alpha)}
    return R, alpha, report


def check_geometry(data: dict) -> dict:
    interval = simplex_facets(1)
    triangle = simplex_facets(2)
    square = product_facets(interval, interval)
    octahedron = (3, Q(4, 3),
                  [(tuple(Q(x, 2) for x in signs), Q(1, 2))
                   for signs in cartesian_product((-1, 1), repeat=3)])
    pairs = [(interval, interval), (interval, triangle),
             (square, triangle), (square, square), (octahedron, interval)]
    tests = 0
    for A, B in pairs:
        ra, aa, _ = measure(A)
        rb, ab, _ = measure(B)
        rp, ap, _ = measure(product_facets(A, B))
        require(rp == ra*rb and ap == (A[0]*aa+B[0]*ab)/(A[0]+B[0]),
                "direct product-minor test failed")
        rj, aj, _ = measure(join_facets(A, B))
        require(rj == join_coefficient(A[0], B[0])*ra*rb*(aa+ab)
                and aj == aa*ab/(aa+ab), "direct join-minor test failed")
        tests += 2
    for A in (interval, triangle, square, octahedron):
        r, a, _ = measure(A)
        rp, ap, _ = measure(pyramid_facets(A))
        d = A[0]
        require(rp == Q((d+1)**d, d**d)*r*(1+a) and ap == a/(1+a),
                "direct pyramid-minor test failed")
        tests += 1
    body = product_facets(simplex_facets(4), simplex_facets(4))
    for _ in range(6):
        body = pyramid_facets(body)
    value, alpha, report = measure(body)
    require(body[0] == 14 and value/simplex_value(14) == Q(385, 384),
            "dimension-fourteen direct determinant witness failed")
    require(alpha == Q(1, 11), "dimension-fourteen lifted ratio failed")
    target = data["explicit_pyramid_witness"]
    require(target["dimension"] == 14 and Q(target["ratio_to_simplex"]) == Q(385, 384)
            and Q(target["a"]) == alpha, "witness metadata mismatch")
    report["facet_data"] = [{"normal": [str(x) for x in u], "support_numerator": str(h)}
                            for u, h in body[2]]
    return {"small_direct_calculus_tests": tests, "dimension_14": report}


def check_family(data: dict) -> dict:
    cert = data["recursive_family"]
    require(len(cert["levels"]) == 7 and cert["comparison_level"] == 6,
            "wrong recursive-family scope")
    n, value, alpha = 5, Q(625, 4), Q(1, 6)
    for j, row in enumerate(cert["levels"]):
        require(row["level"] == j and row["dimension"] == n,
                "recursive dimension mismatch")
        require(Q(row["R"]) == value and Q(row["a"]) == alpha,
                "recursive rational value mismatch")
        require(n == (16*4**j-1)//3 and alpha == Q(1, 6*2**j),
                "closed-form dimensions or lifted invariants failed")
        if j < 6:
            q = 2*n
            # Independent from the producer's g-factorial ratio:
            factor = Q((2*q+1)**(2*q), q**(2*q)*comb(2*q, q))
            value = value**4 * (2*alpha) * factor
            n, alpha = 4*n+1, alpha/2
    lo, hi = Q(cert["limit_lower"]), Q(cert["limit_upper"])
    require(lo == Q(14267, 5000) and hi == Q(5707, 2000), "unexpected endpoints")
    require(cert["comparison_exponent"] == 3*n+1 == 65536, "wrong endpoint exponent")
    require(Q(cert["tail_factor_lower"]) == 3 and Q(cert["tail_factor_upper"]) == 6,
            "unexpected analytic tail factors")
    require(lo**(3*n+1) < 3*value**3, "lower limit endpoint failed")
    require(6*value**3 < hi**(3*n+1), "upper limit endpoint failed")
    comparison = data["old_product_class_comparison"]
    upper = Q(comparison["root_upper"])
    gain = Q(comparison["eventual_exponential_factor"])
    require(upper == Q(561993, 200000) and gain == Q(203, 200), "comparison input mismatch")
    require(simplex_value(13) < upper**13 and lo > gain*upper,
            "comparison with old simplex-product asymptotics failed")
    return {"last_level": 6, "dimension": n, "endpoint_exponent": 3*n+1,
            "limit_lower": str(lo), "limit_upper": str(hi),
            "eventual_exponential_factor_over_v1_1": str(gain)}


def negative_controls(data: dict) -> int:
    bad = deepcopy(data)
    bad["finite_closure"]["levels"][0][0]["R"] = "2"
    tests = [(bad, check_finite)]
    bad = deepcopy(data)
    bad["finite_closure"]["levels"][14].pop()
    tests.append((bad, check_finite))
    bad = deepcopy(data)
    bad["recursive_family"]["levels"][0]["R"] = "1"
    tests.append((bad, check_family))
    bad = deepcopy(data)
    bad["recursive_family"]["limit_lower"] = "3"
    tests.append((bad, check_family))
    for mutated, checker in tests:
        try:
            checker(mutated)
        except (ValueError, IndexError, KeyError):
            continue
        raise ValueError("a corrupted certificate was accepted")
    return len(tests)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path, default=ROOT/"certificates/exact.json")
    parser.add_argument("--report", type=Path, default=ROOT/"results/check.json")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text(encoding="utf-8"))
    require(data["schema"] == "mxym-math-005-join-calculus-v2-exact-1", "unknown schema")
    report = {"finite_class": check_finite(data), "direct_geometry": check_geometry(data),
              "recursive_family": check_family(data)}
    if args.self_test:
        report["corrupted_certificates_rejected"] = negative_controls(data)
    report["scope"] = "Exact finite checking, not external peer review or analytic formalization."
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n", encoding="utf-8")
    print("PASS: exact downward-hull closure in dimensions 0..14;")
    print("      every recursive product/join body has R <= c_n for n <= 13;")
    print("      the dimension-14 optimum is (385/384)c_14.")
    print("PASS: 14 direct low-dimensional calculus tests; all 136 maximal")
    print("      horizontal/lifted minors of the explicit 14D witness checked.")
    print("PASS: independent central-binomial recurrence and exact endpoints")
    print("      2.8534 < Lambda < 2.8535; eventual gain over v1.1 exceeds 1.015^n.")
    if args.self_test:
        print("PASS: four deliberately corrupted certificates rejected.")
    print("SCOPE: paper.md supplies the geometric identities and infinite arguments.")


if __name__ == "__main__":
    main()
