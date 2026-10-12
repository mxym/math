#!/usr/bin/env python3
"""Exact checks for the simplex-product manuscript (standard-library Python).

This program verifies finite rational comparisons and independently enumerates
optimal partitions by dynamic programming. It does not formalize the analytic
concavity argument or any assertion in the similarity manuscript.

No floating-point decisions, third-party solvers, or disableable assertions.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from math import factorial
from pathlib import Path
import json


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def c(n: int) -> Fraction:
    if n < 1:
        raise ValueError("A factor dimension must be positive")
    return Fraction((n + 1) * n**n, factorial(n))


def record(x: Fraction) -> dict[str, str]:
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def strict_record(x: Fraction, name: str) -> dict:
    require(x > 1, name)
    return {**record(x), "positive_integer_margin": str(x.numerator-x.denominator)}


def balanced(n: int, k: int) -> tuple[Fraction, tuple[int, ...]]:
    if not 1 <= k <= n:
        raise ValueError("Require 1 <= k <= n")
    q, r = divmod(n, k)
    parts = (q,) * (k-r) + (q+1,) * r
    return c(q)**(k-r) * c(q+1)**r, parts


def candidates(n: int) -> list[tuple[int, Fraction, tuple[int, ...]]]:
    ks = sorted({max(1, n//13), max(1, (n+12)//13)})
    return [(k, *balanced(n, k)) for k in ks]


def residue(n: int) -> tuple[Fraction, tuple[int, ...]]:
    if n < 100:
        raise ValueError("The residue formula is asserted for n >= 100")
    m, r = divmod(n, 13)
    if r == 0:
        parts = (13,) * m
    elif r <= 8:
        require(m >= r, "Negative fourteen-branch multiplicity")
        parts = (13,) * (m-r) + (14,) * r
    else:
        require(m+r >= 12, "Negative twelve-branch multiplicity")
        parts = (12,) * (13-r) + (13,) * (m+r-12)
    require(sum(parts) == n, "Residue partition dimension")
    value = Fraction(1)
    for d in parts:
        value *= c(d)
    return value, parts


def verify(limit: int) -> dict:
    if not 112 <= limit <= 1000:
        raise ValueError("Require 112 <= limit <= 1000")
    ratios = {
        "root_13_beats_12": c(13)**12 / c(12)**13,
        "root_13_beats_14": c(13)**14 / c(14)**13,
        "strict_concavity_at_13": c(13)**2 / (c(12)*c(14)),
        "residue_8_prefers_14": c(14)**8 / (c(12)**5*c(13)**4),
        "residue_9_prefers_12": c(12)**4*c(13)**6 / c(14)**9,
        "runner_up_14_beats_12": c(14)**6 / c(12)**7,
        "stability_constant_112": c(13)**16*c(12)**13 / c(14)**26,
    }
    certificates = {name: strict_record(ratio, name) for name, ratio in ratios.items()}
    no_ties = {}
    for n in range(14, 100):
        opts = sorted(candidates(n), key=lambda v: v[1])
        if len(opts) == 2:
            loser, winner = opts
            no_ties[str(n)] = {
                "winning_count": winner[0], "losing_count": loser[0],
                **strict_record(winner[1]/loser[1], f"No tie at n={n}")}

    cs = [Fraction(1)] + [c(d) for d in range(1, limit+1)]
    dp = [Fraction(1)]
    # Store all optimal multisets, not just the first maximizing first-part.
    # The test establishes that each set has one element at every checked n.
    all_parts: list[set[tuple[int, ...]]] = [{()}]
    for n in range(1, limit+1):
        best = max(cs[d]*dp[n-d] for d in range(1, n+1))
        winning_parts = set()
        for d in range(1, n+1):
            if cs[d]*dp[n-d] == best:
                for previous in all_parts[n-d]:
                    winning_parts.add(tuple(sorted((d,)+previous)))
        dp.append(best)
        all_parts.append(winning_parts)
        require(len(winning_parts) == 1, f"DP multiset uniqueness at n={n}")
        opts = candidates(n)
        predicted = max(v[1] for v in opts)
        require(predicted == best, f"Two-candidate formula at n={n}")
        counts = [v for v in opts if v[1] == best]
        require(len(counts) == 1, f"Candidate-count uniqueness at n={n}")
        require(counts[0][2] in winning_parts, f"Balanced multiset at n={n}")
        if n >= 100:
            rv, rp = residue(n)
            require(rv == best and rp in winning_parts, f"Residue formula at n={n}")

    require(all(dp[n] == cs[n] for n in range(1, 20)), "First excess lower range")
    require(dp[20] == cs[10]**2 > cs[20], "First excess dimension 20")
    require(dp[99] == cs[12]**5*cs[13]**3, "Exact optimizer at 99")
    require(dp[112] == cs[14]**8 > cs[13]*dp[99], "Sharp threshold obstruction")
    failures = [n for n in range(1, limit-12) if dp[n+13] != cs[13]*dp[n]]
    require(max(failures) == 99, "Last recurrence failure")
    require(all_parts[112] == {(14,)*8}, "Sharp stability example")
    lo, hi = Fraction("2.809964732559"), Fraction("2.809964732560")
    require(lo**13 < cs[13] < hi**13, "Exact rho isolation")
    # Cross-check the sharp runner-up inequality without logarithms for every
    # non-13 block in the finite range: c_d^(14) <= c_14^d.
    for d in range(1, limit+1):
        if d != 13:
            require(cs[d]**14 <= cs[14]**d, f"Runner-up power comparison d={d}")
            require((cs[d]**14 == cs[14]**d) == (d == 14), f"Runner-up equality d={d}")
    examples = {}
    for n in (19, 20, 25, 26, 50, 99, 100, 112, 125):
        if n <= limit:
            examples[str(n)] = {"parts": list(next(iter(all_parts[n]))), "value": record(dp[n])}
    return {
        "status": "PASS", "version": "1.1", "arithmetic": "exact integers and rational numbers",
        "scope": "finite certificates and independent DP cross-check; not proof-assistant formalization",
        "strict_certificates": certificates,
        "finite_no_tie_certificates": no_ties,
        "DP_range_inclusive": [1, limit], "DP_all_optimal_multisets_unique": True,
        "recurrence_failures_in_checked_range": failures,
        "last_recurrence_failure_in_checked_range": 99,
        "rho_interval": {"lower": record(lo), "upper": record(hi), "test": "lower^13 < c13 < upper^13"},
        "sharp_stability_constant": 112,
        "examples": examples,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=300)
    parser.add_argument("--output", type=Path, default=Path("exact_certificate.json"))
    args = parser.parse_args()
    if not 112 <= args.limit <= 1000:
        parser.error("--limit must be between 112 and 1000")
    result = verify(args.limit)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"PASS: seven exact comparisons and {len(result['finite_no_tie_certificates'])} finite no-tie certificates")
    print(f"PASS: independent DP over all partitions in dimensions 1..{args.limit}; every optimizer multiset unique")
    print("PASS: recurrence threshold 100; optimal root 13; sharp dimension-mass stability constant 112")
    print("Scope: finite certificates, not a formal proof of the infinite analytic argument.")


if __name__ == "__main__":
    main()
