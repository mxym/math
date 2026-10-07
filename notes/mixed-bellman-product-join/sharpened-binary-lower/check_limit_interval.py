#!/usr/bin/env python3
"""Exact checker for the certified two-sided binary-T5 limit interval."""

from fractions import Fraction as F
from math import factorial
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def require(cond, msg):
    if not cond:
        raise ArithmeticError(msg)


def atan_series(x, terms):
    s = F(0)
    for k in range(terms):
        s += (1 if k % 2 == 0 else -1) * x ** (2 * k + 1) / (2 * k + 1)
    return s


def exp_lower(y, degree):
    require(y > 0, "positive exponential argument")
    s = term = F(1)
    for k in range(1, degree + 1):
        term *= y / k
        s += term
    return s


def exp_upper(y, degree):
    require(F(0) < y < degree + 2, "geometric exponential-tail gate")
    s = term = F(1)
    for k in range(1, degree + 1):
        term *= y / k
        s += term
    nxt = term * y / (degree + 1)
    return s + nxt / (1 - y / (degree + 2))


def g(n):
    return F(n**n, factorial(n))


# Machin formula. Alternating-series parity makes these rigorous bounds:
# six terms for atan(1/5) are a lower bound, three terms for atan(1/239)
# are an upper bound; reverse the parities for the upper pi bound.
x = F(1, 5)
z = F(1, 239)
pi_lower = 16 * atan_series(x, 6) - 4 * atan_series(z, 3)
pi_upper = 16 * atan_series(x, 7) - 4 * atan_series(z, 4)
require(pi_lower < pi_upper, "pi interval ordering")


# q_j = 2 d_j = (32*4^j-2)/3.
def q(j):
    num = 32 * 4**j - 2
    require(num % 3 == 0, "q integrality")
    return num // 3


# Lower factor for every j >= 7.
# Robbins + log(1+1/(2q)) > 1/(2q)-1/(8q^2) gives
# D_j > (1/3)sqrt((pi/3)(32-2/4^j)) exp(y_-(q_j)),
# y_-(q)=1+2/(12q+1)-7/(24q).
j7 = 7
q7 = q(j7)
y_lower = F(1) + F(2, 12 * q7 + 1) - F(7, 24 * q7)
E_lower = exp_lower(y_lower, 14)
lower_sq = (
    F(1, 9)
    * pi_lower
    * F(32 * 4**j7 - 2, 3 * 4**j7)
    * E_lower**2
)
tail_lower = F(524519195, 100000000)  # 5.24519195
require(lower_sq > tail_lower**2, "uniform lower tail factor")


# Specific upper bound for D_7.
# The extra +1/(12q^2) is the third alternating logarithm term.
y_upper_7 = (
    F(1)
    + F(1, 6 * q7)
    - F(1, 24 * q7 + 1)
    - F(1, 4 * q7)
    + F(1, 12 * q7 * q7)
)
E_upper_7 = exp_upper(y_upper_7, 12)
upper_7_sq = (
    F(1, 9)
    * pi_upper
    * F(32 * 4**j7 - 2, 3 * 4**j7)
    * E_upper_7**2
)
tail_upper_7 = F(5245192, 1000000)  # 5.245192
require(upper_7_sq < tail_upper_7**2, "D_7 upper factor")


# Uniform upper bound for every j >= 8.
# Discard 32-2/4^j < 32, use (1+1/(2q))^(2q) < e, and
# u(q)=1/(6q)-1/(24q+1), which is decreasing.
q8 = q(8)
y_upper_8 = F(1) + F(1, 6 * q8) - F(1, 24 * q8 + 1)
E_upper_8 = exp_upper(y_upper_8, 12)
upper_tail_sq = F(32, 27) * pi_upper * E_upper_8**2
tail_upper_8 = F(5245207, 1000000)  # 5.245207
require(upper_tail_sq < tail_upper_8**2, "uniform j>=8 upper tail factor")


# Reconstruct R_7 exactly from the inherited T5 recurrence.
d = 5
a = F(1, 6)
R = F(625, 4)
for _ in range(7):
    D = 2 * a * g(4 * d + 1) / g(2 * d) ** 2
    R = R**4 * D
    d = 4 * d + 1
    a /= 2

require(d == 87381, "d_7 mismatch")
E7 = 3 * d + 1
require(E7 == 262144, "E_7 mismatch")


# Lower endpoint:
# Lambda^E7 > R_7^3 * tail_lower.
lower_endpoint = F(2853465550695797, 10**15)
lhs = (
    lower_endpoint.numerator**E7
    * R.denominator**3
    * tail_lower.denominator
)
rhs = (
    lower_endpoint.denominator**E7
    * R.numerator**3
    * tail_lower.numerator
)
require(lhs < rhs, "lower endpoint comparison")


# Upper endpoint. Since E_8=4 E_7 and R_8=R_7^4 D_7,
# Lambda^E8 < R_7^12 * tail_upper_7^3 * tail_upper_8.
E8 = 4 * E7
require(E8 == 1048576, "E_8 mismatch")
upper_endpoint = F(2853465550704, 10**12)
lhs = (
    R.numerator**12
    * tail_upper_7.numerator**3
    * tail_upper_8.numerator
    * upper_endpoint.denominator**E8
)
rhs = (
    R.denominator**12
    * tail_upper_7.denominator**3
    * tail_upper_8.denominator
    * upper_endpoint.numerator**E8
)
require(lhs < rhs, "upper endpoint comparison")

print("PASS: D_j > 5.24519195 for every j >= 7.")
print("PASS: D_7 < 5.245192 and D_j < 5.245207 for every j >= 8.")
print("PASS: exact T5 recurrence reconstructed through d_7 = 87381.")
print("PASS: 2.853465550695797 < Lambda_(2,5) < 2.853465550704.")
