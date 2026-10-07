#!/usr/bin/env python3
"""Exact checker for the sharpened binary-T5 lower endpoint."""

from fractions import Fraction as F
from math import factorial
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def require(cond, msg):
    if not cond:
        raise ArithmeticError(msg)


def g(n):
    return F(n ** n, factorial(n))


# Machin: pi = 16 atan(1/5) - 4 atan(1/239).
# Four alternating terms give a lower bound for atan(1/5);
# atan(x) < x for x>0 gives the needed upper bound on atan(1/239).
x = F(1, 5)
atan5_lower = x - x**3 / 3 + x**5 / 5 - x**7 / 7
pi_lower = 16 * atan5_lower - F(4, 239)
require(pi_lower > F(333, 106), "pi lower bound failed")

J = 7
pow4 = 4**J
n7 = (64 * pow4 - 4) // 3
require(n7 == 349524, "n7 mismatch")
y = F(1) - F(1, 2 * n7)

# Positive Taylor lower bound for exp(y).
E8 = F(1)
term = F(1)
for k in range(1, 9):
    term *= y / k
    E8 += term

tail_sq = (
    F(1, 9)
    * F(333, 106)
    * F(32 * pow4 - 2, 3 * pow4)
    * E8**2
)
require(
    tail_sq > F(1049, 200) ** 2,
    "uniform D_j > 1049/200 tail inequality failed",
)

# Reconstruct the exact binary T5 recurrence through level 7.
d = 5
a = F(1, 6)
R = F(625, 4)
for _ in range(J):
    D = 2 * a * g(4 * d + 1) / (g(2 * d) ** 2)
    R = R**4 * D
    d = 4 * d + 1
    a /= 2

require(d == 87381, "d7 mismatch")
require(a == F(1, 768), "a7 mismatch")
exponent = 3 * d + 1
require(exponent == 262144, "endpoint exponent mismatch")

endpoint = F(14267327751, 5000000000)  # 2.8534655502
tail_constant = F(1049, 200)

# Clear positive denominators exactly.
lhs = (
    endpoint.numerator**exponent
    * R.denominator**3
    * tail_constant.denominator
)
rhs = (
    endpoint.denominator**exponent
    * R.numerator**3
    * tail_constant.numerator
)
require(lhs < rhs, "2.8534655502 endpoint inequality failed")

print("PASS: D_j > 1049/200 for every j >= 7 by the analytic tail bound.")
print("PASS: exact binary-T5 state reconstructed through d_7 = 87381.")
print("PASS: Lambda_(2,5) > 2.8534655502.")
