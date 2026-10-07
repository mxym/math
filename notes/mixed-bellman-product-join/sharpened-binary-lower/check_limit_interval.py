#!/usr/bin/env python3
"""Exact checker for the certified two-sided binary-T5 limit interval.

Endpoint comparisons use rigorous rational logarithm intervals rather than
materializing multi-million-digit powers.
"""

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


def log_unit_interval(y, terms):
    """Rigorous log interval for rational 1 <= y <= 2 via atanh series."""
    require(F(1) <= y <= F(2), "unit log range")
    z = (y - 1) / (y + 1)
    total = F(0)
    zpow = z
    for j in range(terms):
        if j:
            zpow *= z * z
        total += zpow / (2 * j + 1)
    lower = 2 * total
    upper = lower + 2 * z ** (2 * terms + 1) / (
        (2 * terms + 1) * (1 - z * z)
    )
    return lower, upper


LOG2 = log_unit_interval(F(2), 40)


def log_int_interval(n, bits=96, terms=32):
    """Rigorous log interval using only the leading bits of a positive integer."""
    require(isinstance(n, int) and n > 0, "positive integer logarithm")
    k = n.bit_length() - 1
    if k >= bits:
        a = n >> (k - bits)
        y_lower = F(a, 1 << bits)
        y_upper = F(a + 1, 1 << bits)
    else:
        y_lower = y_upper = F(n, 1 << k)
    lower_unit, _ = log_unit_interval(y_lower, terms)
    _, upper_unit = log_unit_interval(y_upper, terms)
    return k * LOG2[0] + lower_unit, k * LOG2[1] + upper_unit


def log_fraction_interval(x):
    """Rigorous log interval for a positive Fraction."""
    require(x > 0, "positive rational logarithm")
    num_lower, num_upper = log_int_interval(x.numerator)
    den_lower, den_upper = log_int_interval(x.denominator)
    return num_lower - den_upper, num_upper - den_lower


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


# Endpoint comparisons are equivalent to huge integer-power inequalities.
# We replay them faster through rigorous rational log intervals.  The atanh
# remainder and the leading-bit enclosure are both one-sided exact bounds.
log_R = log_fraction_interval(R)

# Lower endpoint:
# Lambda^E7 > R_7^3 * tail_lower.
lower_endpoint = F(2853465550695797, 10**15)
log_lower_endpoint = log_fraction_interval(lower_endpoint)
log_tail_lower = log_fraction_interval(tail_lower)
lower_margin = (
    3 * log_R[0]
    + log_tail_lower[0]
    - E7 * log_lower_endpoint[1]
)
require(lower_margin > 0, "lower endpoint comparison")


# Upper endpoint. Since E_8=4 E_7 and R_8=R_7^4 D_7,
# Lambda^E8 < R_7^12 * tail_upper_7^3 * tail_upper_8.
E8 = 4 * E7
require(E8 == 1048576, "E_8 mismatch")
upper_endpoint = F(2853465550704, 10**12)
log_upper_endpoint = log_fraction_interval(upper_endpoint)
log_tail_upper_7 = log_fraction_interval(tail_upper_7)
log_tail_upper_8 = log_fraction_interval(tail_upper_8)
upper_margin = (
    E8 * log_upper_endpoint[0]
    - 12 * log_R[1]
    - 3 * log_tail_upper_7[1]
    - log_tail_upper_8[1]
)
require(upper_margin > 0, "upper endpoint comparison")

print("PASS: D_j > 5.24519195 for every j >= 7.")
print("PASS: D_7 < 5.245192 and D_j < 5.245207 for every j >= 8.")
print("PASS: exact T5 recurrence reconstructed through d_7 = 87381.")
print("PASS: 2.853465550695797 < Lambda_(2,5) < 2.853465550704.")
