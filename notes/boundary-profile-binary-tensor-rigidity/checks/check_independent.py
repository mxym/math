#!/usr/bin/env python3
"""Second exact implementation of the explicit corollary.

This does not import check_exact.py.  It uses a different exponential
majorant:  exp(L) is bounded below by its positive Taylor polynomial, hence
exp(-L) is bounded above by the reciprocal.
"""
from fractions import Fraction
from math import factorial
import json

b = Fraction(4627, 3125)
d = -Fraction(58, 125)
S = Fraction(1) + b*b + 2*d*d
M1 = b*b + 4*d*d
B = b*b + 2*d
C = d*d
L = Fraction(1473, 5000)
U = Fraction(29461, 100000)
target = Fraction(311793, 500000)

def critical(y):
    return (B-1) + (2*C-B)*y - C*y*y

checks = {
    "critical_left_positive": critical(L) > 0,
    "critical_right_negative": critical(U) < 0,
    "critical_derivative_negative": 2*C-B < 0,
    "factor_increasing": B > 0 and C > 0,
}
# Positive Taylor polynomial for e^L gives a strict lower bound for e^L.
N = 8
expL_lower = sum(L**n / Fraction(factorial(n)) for n in range(N+1))
expminusL_upper = 1 / expL_lower
profile_upper = 2*expminusL_upper*(1+B*U+C*U*U)
num = 2*S-profile_upper
checks["positive_distance_limit_lower"] = num > 0
checks["target_bound"] = num*num > 16*target**4*S*M1
checks["old_constant_improved"] = target**4 > Fraction(1, 8)
delta_two_band = target*target - Fraction(2, 7)
checks["concurrent_two_band_improved"] = (
    delta_two_band > 0 and delta_two_band*delta_two_band > Fraction(1, 98)
)

if not all(checks.values()):
    raise SystemExit("FAILED: " + ", ".join(k for k,v in checks.items() if not v))

print(json.dumps({
    "method": "reciprocal-positive-Taylor",
    "degree": N,
    "profile_upper": [profile_upper.numerator, profile_upper.denominator],
    "target": [target.numerator, target.denominator],
    "checks": checks,
}, indent=2, sort_keys=True))
