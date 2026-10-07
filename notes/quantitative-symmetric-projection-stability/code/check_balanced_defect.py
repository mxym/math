#!/usr/bin/env python3
"""Exact regression for the quantitative balanced Rademacher defect lemma.

This finite regression checks all 4,930 balanced denominator-30 coefficient
multisets with 4 through 8 coefficients, allowing zeros. It supplements the
balanced Rademacher lemma in paper.md; it does not replace that proof.

Run with Python 3.10 or newer, ordinarily or with ``python3 -O``. All checks use
explicit exceptions, so optimization cannot remove them. No third-party
packages are required.
"""

from fractions import Fraction
from itertools import combinations_with_replacement, product
import json


def sign_average(coefficients):
    """Return the exact Rademacher absolute first moment."""
    return Fraction(
        sum(
            abs(sum(sign * value for sign, value in zip(signs, coefficients)))
            for signs in product((-1, 1), repeat=len(coefficients))
        ),
        2 ** len(coefficients),
    )


def verify():
    denominator = 30
    counts = {}
    total = 0
    for coefficient_count in range(4, 9):
        count = 0
        for coefficients in combinations_with_replacement(
            range(denominator // 2 + 1), coefficient_count
        ):
            if sum(coefficients) != denominator:
                continue
            ordered = tuple(reversed(coefficients))
            defect = Fraction(denominator, 2) - sign_average(ordered)
            lower_bound = min(
                Fraction(ordered[3], 2),
                Fraction(denominator // 2 - ordered[0], 4),
            )
            if defect < lower_bound:
                raise RuntimeError(
                    "Balanced-defect bound failed: "
                    f"coefficients={ordered}, defect={defect}, "
                    f"lower_bound={lower_bound}"
                )
            count += 1
        counts[str(coefficient_count)] = count
        total += count

    if total != 4930:
        raise RuntimeError(f"Unexpected case count: {total}, expected 4930")

    # These guards catch the two branches that must remain separate.
    four_equal = (Fraction(1, 4),) * 4
    if sign_average(four_equal) != Fraction(3, 8):
        raise RuntimeError("Four-equal strict-defect guard failed")
    half_mass = (Fraction(1, 2),) + (Fraction(1, 6),) * 3
    if sign_average(half_mass) != Fraction(1, 2):
        raise RuntimeError("Half-mass equality guard failed")

    return {
        "status": "passed",
        "denominator": denominator,
        "coefficient_counts": counts,
        "total_cases": total,
        "four_equal_defect": "1/8",
        "half_mass_defect": "0",
        "checks_survive_python_optimization": True,
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, indent=2))
