#!/usr/bin/env python3
from fractions import Fraction
from math import factorial
import json

# Explicit three-term profile:
# A(x)=1+b*x+d*x^2, corresponding to
# (a0,a1,a2)=(1,b,sqrt(2)*d) in the normalized basis x^k/sqrt(k!).
b = Fraction(4627, 3125)
d = Fraction(-58, 125)

S = 1 + b*b + 2*d*d
M1 = b*b + 4*d*d
B = 2*d + b*b
C = d*d

# For F(y)=2 exp(-y)(1+B y+C y^2),
# F'(y)/(2 exp(-y)) = q(y).
def q(y: Fraction) -> Fraction:
    return (B - 1) + (2*C - B)*y - C*y*y

L = Fraction(1473, 5000)       # 0.2946
U = Fraction(29461, 100000)    # 0.29461

checks = {}
checks["B_gt_1"] = B > 1
checks["C_pos"] = C > 0
checks["qprime_negative_on_nonnegative_axis"] = 2*C - B < 0
checks["q_L_pos"] = q(L) > 0
checks["q_U_neg"] = q(U) < 0
checks["root_bracket_ordered"] = 0 < L < U

# Since 0<L<1, the alternating series for exp(-L) has decreasing term
# magnitudes. An even partial sum is an upper bound.
N = 10
if N % 2:
    raise SystemExit("Taylor degree must be even")
exp_upper = sum(
    ((-1)**n) * L**n / Fraction(factorial(n), 1)
    for n in range(N + 1)
)
next_term_abs = L**(N + 1) / Fraction(factorial(N + 1), 1)
checks["alternating_terms_decrease"] = 0 < L < 1
checks["exp_upper_positive"] = exp_upper > 0
checks["next_term_positive"] = next_term_abs > 0

poly_U = 1 + B*U + C*U*U
M_upper = 2 * exp_upper * poly_U
numerator_lower = 2*S - M_upper

# J=(2S-M)/(4 sqrt(S M1)); the asymptotic C_p/p^(1/4)
# lower constant is sqrt(J). Prove sqrt(J)>c without irrational arithmetic:
# numerator^2 > 16 c^4 S M1.
c = Fraction(311793, 500000)  # 0.623586
checks["numerator_positive"] = numerator_lower > 0
margin = numerator_lower*numerator_lower - 16*c**4*S*M1
checks["constant_bound"] = margin > 0
checks["strictly_improves_old_constant"] = c**4 > Fraction(1, 8)
two_band_delta = c*c - Fraction(2, 7)
checks["strictly_improves_concurrent_two_band"] = (
    two_band_delta > 0 and two_band_delta*two_band_delta > Fraction(1, 98)
)

if not all(checks.values()):
    failed = [k for k, v in checks.items() if not v]
    raise SystemExit("FAILED: " + ", ".join(failed))

def dec(fr: Fraction, places=15):
    # Diagnostic only; no proof decision uses decimal arithmetic.
    sign = "-" if fr < 0 else ""
    fr = abs(fr)
    scale = 10**places
    qv = (fr.numerator * scale) // fr.denominator
    return f"{sign}{qv//scale}.{qv%scale:0{places}d}"

report = {
    "profile": {
        "b": [b.numerator, b.denominator],
        "d": [d.numerator, d.denominator],
        "S": [S.numerator, S.denominator],
        "M1": [M1.numerator, M1.denominator],
        "B": [B.numerator, B.denominator],
        "C": [C.numerator, C.denominator],
    },
    "critical_root_bracket": {
        "L": [L.numerator, L.denominator],
        "U": [U.numerator, U.denominator],
        "q_L": [q(L).numerator, q(L).denominator],
        "q_U": [q(U).numerator, q(U).denominator],
    },
    "exp_upper": {
        "degree": N,
        "value": [exp_upper.numerator, exp_upper.denominator],
        "decimal_floor": dec(exp_upper),
    },
    "projection_upper": {
        "value": [M_upper.numerator, M_upper.denominator],
        "decimal_floor": dec(M_upper),
    },
    "target_constant": {
        "c": [c.numerator, c.denominator],
        "decimal": "0.623586",
        "squared_rational_test_margin_num": margin.numerator,
        "squared_rational_test_margin_den": margin.denominator,
    },
    "checks": checks,
}
print(json.dumps(report, indent=2, sort_keys=True))
