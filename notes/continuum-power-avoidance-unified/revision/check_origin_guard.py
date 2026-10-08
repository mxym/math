#!/usr/bin/env python3
"""Exact window-count interface controls; no floats and no assert statements."""
from fractions import Fraction
from pathlib import Path
import json

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def open_count(first, step, u, length):
    # n>=0, first+step*n belongs to (u,u+length).
    if step <= 0 or length <= 0:
        raise ValueError("Positive gap and window length required")
    left, right = Fraction(u-first, step), Fraction(u+length-first, step)
    n_min = max(0, left.numerator//left.denominator + 1)
    n_max = -((-right.numerator)//right.denominator) - 1
    return max(0, n_max-n_min+1)

first, step, D, eta, length = 1000, 5, 12, Fraction(1,24), 24
early_count = open_count(first, step, 4, length)
require(early_count == 0, "Early empty-window countercontrol failed")
require(early_count < eta*length, "Missing-origin lower bound was not refuted")
# The same first sample has worst-parameter starting position s1*z1=2000.
# Check both exponent endpoints and equality of either open-window endpoint.
checked = []
for s in [1,2]:
    w_first, w_step = s*first, s*step
    for u in [2000,2005,2010,2024]:
        count = open_count(w_first,w_step,u,length)
        require(Fraction(count) >= eta*length, "Guarded lower count failed")
        require(Fraction(count) <= 1+Fraction(length,3), "Separation upper count failed")
        checked.append({"s":s,"u":u,"count":count})
# Empty local tests have failure probability exactly one. For lambda=6,
# L>=24, positivity of lambda*L gives exp(-lambda*L)<1 mathematically.
require(6*length > 0, "Strict exponent comparison lost")
report = {"status":"PASS","optimization_active":not __debug__,
          "early_window":{"u":4,"length":length,"first":first,"step":step,
                          "actual_count":early_count,"claimed_lower":"1",
                          "old_lower_count_refuted":True,
                          "empty_test_miss_probability":"1",
                          "old_claimed_factor":"exp(-144) < 1"},
          "guarded_endpoint_cases":checked,
          "scope":"Exact count interfaces; symbolic full-tree counterexample is in REVIEW.txt."}
mode = "optimized" if not __debug__ else "normal"
(Path(__file__).parent/f"origin-guard-{mode}.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
