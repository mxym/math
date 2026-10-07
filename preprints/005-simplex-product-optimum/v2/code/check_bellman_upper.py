#!/usr/bin/env python3
"""Exact rational-interval verifier for BELLMAN_UPPER_BOUND.md.

Proof decisions use only integers and fractions.Fraction.  Floating point is
used only, if requested, for human-readable printing after all assertions.

The mathematical reduction from products/joins to the scalar inequalities
checked here is in BELLMAN_UPPER_BOUND.md.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise ValueError(msg)


# ---------- exact log and pi intervals ----------

SERIES_N = 32
ALPHA_N = 70


def log2_bounds(n: int = SERIES_N) -> tuple[Q, Q]:
    z = Q(1, 3)
    zz = z * z
    total = Q(0)
    power = z
    for j in range(n):
        total += power / (2 * j + 1)
        power *= zz
    lower = 2 * total
    tail = 2 * z ** (2 * n + 1) / ((2 * n + 1) * (1 - zz))
    return lower, lower + tail


LOG2 = log2_bounds()


def log_bounds(x: Q, n: int = SERIES_N) -> tuple[Q, Q]:
    """Rigorous rational enclosure for log(x), x>0."""
    require(x > 0, "log input must be positive")
    num, den = x.numerator, x.denominator
    k = num.bit_length() - den.bit_length()
    y = x / Q(2**k) if k >= 0 else x * Q(2 ** (-k))
    while y < 1:
        k -= 1
        y *= 2
    while y >= 2:
        k += 1
        y /= 2
    z = (y - 1) / (y + 1)
    require(0 <= z <= Q(1, 3), "range reduction failed")
    zz = z * z
    total = Q(0)
    power = z
    for j in range(n):
        total += power / (2 * j + 1)
        power *= zz
    ly_lower = 2 * total
    tail = Q(0) if z == 0 else 2 * z ** (2 * n + 1) / (
        (2 * n + 1) * (1 - zz)
    )
    ly_upper = ly_lower + tail
    if k >= 0:
        return k * LOG2[0] + ly_lower, k * LOG2[1] + ly_upper
    return k * LOG2[1] + ly_lower, k * LOG2[0] + ly_upper


def arctan_bounds(x: Q, n: int) -> tuple[Q, Q]:
    """Alternating-series enclosure for arctan(x), 0<x<=1."""
    require(0 < x <= 1, "arctan range")
    total = Q(0)
    power = x
    for j in range(n):
        term = power / (2 * j + 1)
        total = total + term if j % 2 == 0 else total - term
        power *= x * x
    next_mag = power / (2 * n + 1)
    if n % 2 == 0:
        return total, total + next_mag
    return total - next_mag, total


def pi_bounds() -> tuple[Q, Q]:
    a_lo, a_hi = arctan_bounds(Q(1, 5), 32)
    b_lo, b_hi = arctan_bounds(Q(1, 239), 10)
    return 16 * a_lo - 4 * b_hi, 16 * a_hi - 4 * b_lo


PI_I = pi_bounds()
LOG_189_I = log_bounds(Q(189, 128), ALPHA_N)
ALPHA_I = (Q(11, 85) * LOG_189_I[0], Q(11, 85) * LOG_189_I[1])


# ---------- interval helpers ----------

def iadd(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    return a[0] + b[0], a[1] + b[1]


def isub(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    return a[0] - b[1], a[1] - b[0]


def iscale(c: Q | int, a: tuple[Q, Q]) -> tuple[Q, Q]:
    c = Q(c)
    return (c * a[0], c * a[1]) if c >= 0 else (c * a[1], c * a[0])


def imul(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    vals = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(vals), max(vals)


# ---------- fast exact finite log A_{r,s} ----------

@lru_cache(None)
def log_integer_bounds(m: int) -> tuple[Q, Q]:
    require(m >= 1, "integer log input")
    if m == 1:
        return Q(0), Q(0)
    k = m.bit_length() - 1
    y = Q(m, 2**k)
    z = (y - 1) / (y + 1)
    zz = z * z
    total = Q(0)
    power = z
    for j in range(SERIES_N):
        total += power / (2 * j + 1)
        power *= zz
    lower = 2 * total
    tail = Q(0) if z == 0 else 2 * z ** (2 * SERIES_N + 1) / (
        (2 * SERIES_N + 1) * (1 - zz)
    )
    return k * LOG2[0] + lower, k * LOG2[1] + lower + tail


@lru_cache(None)
def log_A_bounds_small_s(r: int, s: int) -> tuple[Q, Q]:
    """Exact interval for log(g(r)g(s)/g(r+s)), used only for s<=9."""
    require(1 <= s <= r, "finite strip ordering")
    n = r + s
    out = (Q(0), Q(0))
    # log binomial(r+s,s)
    for i in range(1, s + 1):
        out = iadd(out, isub(log_integer_bounds(r + i), log_integer_bounds(i)))
    out = iadd(out, iscale(r, log_integer_bounds(r)))
    out = iadd(out, iscale(s, log_integer_bounds(s)))
    out = isub(out, iscale(n, log_integer_bounds(n)))
    return out


def g_fraction(n: int) -> Q:
    if n == 0:
        return Q(1)
    # only tiny n are used in exact identities/tails
    import math
    return Q(n**n, math.factorial(n))


# ---------- exact q_{r,s}(B) branches ----------

def boundary_coefficients(r: int, s: int, b: int) -> tuple[Q, Q, Q]:
    """Coefficients A,D,E in q_b(B)=A B^2 + D B + E."""
    r, s, b = Q(r), Q(s), Q(b)
    den1 = r * r * s + r * s * s + 2 * r * s + s * s + s
    A = (3 * r * r + 3 * r * s + 2 * r + s * s + s) / den1
    D = (-6 * b * r * r - 2 * b * r * s - 4 * b * r) / den1
    denE = (
        r * r * s * s
        + r * r * s
        + r * s**3
        + 3 * r * s * s
        + 2 * r * s
        + s**3
        + 2 * s * s
        + s
    )
    E = (4 * b * b * r * r * s + 3 * b * b * r * r
         + 3 * b * b * r * s + 2 * b * b * r) / denE
    return A, D, E


def branch_data(r: int, s: int):
    require(r >= s >= 1, "branch ordering")
    n = r + s
    Delta = Q(4 * r * s + 3 * r + 3 * s + 2)
    Bminus = Delta / ((s + 1) * (3 * r + s + 2))
    Bplus = Delta / (3 * r + s + 2)
    Bmax = Q(n + 2 * r * s, n)
    require(1 <= Bminus <= Bplus <= Bmax, "bad B thresholds")
    out = []
    if Bminus > 1:
        out.append(("low", Q(1), min(Bminus, Bmax),
                    *boundary_coefficients(r, s, 1)))
    lo, hi = max(Q(1), Bminus), min(Bplus, Bmax)
    if lo <= hi:
        k = Q(3 * n + 2, 4 * r * s + 3 * n + 2)
        out.append(("mid", lo, hi, k, Q(0), Q(0)))
    if Bplus < Bmax:
        out.append(("high", max(Bplus, Q(1)), Bmax,
                    *boundary_coefficients(r, s, s + 1)))
    return out


# ---------- concave branch certification ----------

def derivative_interval(B: Q, A: Q, D: Q) -> tuple[Q, Q]:
    # f'(B)=1/B-alpha(2AB+D)
    T = 2 * A * B + D
    prod = imul(ALPHA_I, (T, T))
    return Q(1) / B - prod[1], Q(1) / B - prod[0]


def q_interval(lo: Q, hi: Q, A: Q, D: Q, E: Q) -> tuple[Q, Q]:
    vertex = -D / (2 * A)
    pts = [lo, hi]
    if lo <= vertex <= hi:
        pts.append(vertex)
    vals = [A * x * x + D * x + E for x in pts]
    qmin = min(vals)
    qmax = max(A * lo * lo + D * lo + E, A * hi * hi + D * hi + E)
    return qmin, qmax


def f_upper(logA_upper: Q, lo: Q, hi: Q, A: Q, D: Q, E: Q) -> Q:
    logB_upper = log_bounds(hi)[1]
    qlo, qhi = q_interval(lo, hi, A, D, E)
    prod = imul(ALPHA_I, (qlo - 1, qhi - 1))
    return logA_upper + logB_upper - prod[0]


def certify_branch(r: int, s: int, lo: Q, hi: Q, A: Q, D: Q, E: Q):
    logA_upper = log_A_bounds_small_s(r, s)[1]
    dlo = derivative_interval(lo, A, D)
    dhi = derivative_interval(hi, A, D)

    if dlo[1] <= 0:
        return f_upper(logA_upper, lo, lo, A, D, E), lo, lo
    if dhi[0] >= 0:
        return f_upper(logA_upper, hi, hi, A, D, E), hi, hi

    require(dlo[0] > 0 and dhi[1] < 0,
            f"derivative endpoint uncertainty at {(r,s)}")
    left, right = lo, hi
    for _ in range(70):
        mid = (left + right) / 2
        dm = derivative_interval(mid, A, D)
        if dm[0] > 0:
            left = mid
        elif dm[1] < 0:
            right = mid
        else:
            # ALPHA_I is far narrower than required by the final margins.
            # Keeping the current enclosing bracket is rigorous.
            break
    return f_upper(logA_upper, left, right, A, D, E), left, right


# ---------- analytic tails ----------

def log_g_bounds(s: int) -> tuple[Q, Q]:
    return log_bounds(g_fraction(s), ALPHA_N)


def certify_quadratic_given_logA_upper(
    logA_upper: Q, lo: Q, hi: Q, A: Q, D: Q, E: Q
) -> Q:
    dlo = derivative_interval(lo, A, D)
    dhi = derivative_interval(hi, A, D)
    if dlo[1] <= 0:
        return f_upper(logA_upper, lo, lo, A, D, E)
    if dhi[0] >= 0:
        return f_upper(logA_upper, hi, hi, A, D, E)
    require(dlo[0] > 0 and dhi[1] < 0, "tail derivative uncertainty")
    left, right = lo, hi
    for _ in range(90):
        mid = (left + right) / 2
        dm = derivative_interval(mid, A, D)
        if dm[0] > 0:
            left = mid
        elif dm[1] < 0:
            right = mid
        else:
            break
    return f_upper(logA_upper, left, right, A, D, E)


def check_tails() -> dict:
    a_lo, a_hi = ALPHA_I
    p_lo, _ = PI_I

    # s>=10
    log2360_hi = log_bounds(Q(23, 60), ALPHA_N)[1]
    logpi_lo = log_bounds(p_lo, ALPHA_N)[0]
    logalpha_lo = log_bounds(a_lo, ALPHA_N)[0]
    tail10 = (
        Q(1, 2) * (log2360_hi - logpi_lo - logalpha_lo)
        - Q(1, 2) + a_hi
    )
    require(tail10 < 0, "s>=10 tail failed")

    small = {}
    for s in (1, 4, 5, 6, 7, 8, 9):
        logA_upper = log_g_bounds(s)[1] - s + Q(s * s, 2000)
        k = Q(3, 4 * s + 3)
        if s == 1:
            B = Q(3)
            prod = imul(ALPHA_I, (k * B * B, k * B * B))
            upper = logA_upper + log_bounds(B, ALPHA_N)[1] - prod[0] + a_hi
        else:
            # unrestricted max of log B - alpha*k B^2
            log_2ak_lo = log_bounds(2 * k * a_lo, ALPHA_N)[0]
            upper = logA_upper - Q(1, 2) - Q(1, 2) * log_2ak_lo + a_hi
        require(upper < 0, f"fixed-side tail failed for s={s}")
        small[str(s)] = str(upper)

    special = {}
    for s in (2, 3):
        logA_upper = log_g_bounds(s)[1] - s + Q(s * s, 2000)
        k = Q(3, 4 * s + 3)
        Bmid = Q(4 * s + 3, 3)
        prod = imul(ALPHA_I, (k * Bmid * Bmid, k * Bmid * Bmid))
        mid_upper = (
            logA_upper + log_bounds(Bmid, ALPHA_N)[1] - prod[0] + a_hi
        )
        require(mid_upper < 0, f"middle tail failed s={s}")

        if s == 2:
            A, D, E, lo, hi = Q(3, 2), Q(-9), Q(33, 2), Q(3), Q(5)
        else:
            A, D, E, lo, hi = Q(1), Q(-8), Q(20), Q(4), Q(7)
        high_upper = certify_quadratic_given_logA_upper(
            logA_upper, lo, hi, A, D, E
        )
        require(high_upper < 0, f"high tail failed s={s}")
        special[str(s)] = {
            "middle_upper": str(mid_upper),
            "high_upper": str(high_upper),
        }

    # e^(1+alpha)<2.8589, checked after taking logs
    log_target_lo = log_bounds(Q(28589, 10000), ALPHA_N)[0]
    require(1 + a_hi < log_target_lo, "2.8589 comparison failed")

    return {
        "s_ge_10_upper": str(tail10),
        "fixed_small_side_upper": small,
        "special_s_2_3": special,
        "log_2_8589_lower_minus_1_plus_alpha_upper":
            str(log_target_lo - (1 + a_hi)),
    }


def check_finite_strip() -> dict:
    # cache all integer log intervals once
    for m in range(1, 1010):
        log_integer_bounds(m)

    worst = None
    branches = 0
    equality_checked = False

    for s in range(1, 10):
        for r in range(s, 1000):
            for name, lo, hi, A, D, E in branch_data(r, s):
                branches += 1

                if (r, s, name) == (5, 5, "mid"):
                    dhi = derivative_interval(hi, A, D)
                    require(dhi[0] > 0 and hi == 6,
                            "equality branch maximum is not the endpoint")
                    require(
                        g_fraction(5) * g_fraction(5) / g_fraction(10) * hi
                        == Q(189, 128),
                        "equality logarithm ratio mismatch",
                    )
                    require(A * hi * hi + D * hi + E - 1 == Q(85, 11),
                            "equality Bellman gap mismatch")
                    equality_checked = True
                    continue

                upper, left, right = certify_branch(r, s, lo, hi, A, D, E)
                require(upper < 0, f"finite branch failed: {(r,s,name)}")
                if worst is None or upper > worst[0]:
                    worst = (upper, r, s, name, left, right)

    require(equality_checked, "T5xT5 equality not checked")
    require(branches == 26847, f"unexpected branch count: {branches}")
    require(worst is not None, "no strict branch")
    return {
        "branches": branches,
        "unique_product_equality": "r=s=5, B=6",
        "worst_strict_upper": str(worst[0]),
        "worst_strict_branch": [worst[1], worst[2], worst[3]],
        "maximizer_bracket": [str(worst[4]), str(worst[5])],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=None)
    args = parser.parse_args()

    finite = check_finite_strip()
    tails = check_tails()
    report = {
        "status": "PASS",
        "arithmetic": "integer and Fraction interval arithmetic",
        "alpha_definition": "(11/85)*log(189/128)",
        "alpha_interval": [str(ALPHA_I[0]), str(ALPHA_I[1])],
        "pi_interval": [str(PI_I[0]), str(PI_I[1])],
        "finite_strip": finite,
        "analytic_tails": tails,
        "conclusion":
            "Gamma_C <= e*(189/128)^(11/85) < 2.8589; lower bound 2.8534 is checked in the v2 self-similar certificate.",
    }
    if args.report is not None:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print("PASS: 26,847 finite Bellman branches certified.")
    print("PASS: unique product equality is T5 x T5 at B=6.")
    print("PASS: analytic tails s>=10 and r>=1000 for s<=9 certified.")
    print("PASS: Gamma_C <= e*(189/128)^(11/85) < 2.8589.")


if __name__ == "__main__":
    main()
