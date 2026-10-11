#!/usr/bin/env python3
"""Exact algebra checks for the two-storage hydrology identifiability note."""
from fractions import Fraction as F


def need(ok, msg):
    if not ok:
        raise SystemExit("FAIL: " + msg)


def output_operator(a, b, c):
    # Q'' + S Q' + P Q = a p' + P p
    return a + b + c, a * c


def jet_zero_state(a, b, c, p):
    B = a + b
    return a * p, -a * B * p, a * p * (B * B + b * c)


def main():
    a, b, c, p = map(F, (2, 2, 2, 3))
    q1, q2, q3 = jet_zero_state(a, b, c, p)
    need(q1 / p == a, "first derivative recovery")
    B = -q2 / q1
    need(B == a + b, "second derivative recovery")
    bc = q3 / q1 - B * B
    need(bc == b * c, "third derivative recovery")
    need(B - a == b and bc / b == c, "all rates recovered")

    # Equal output equation but distinct physical parameterizations.
    left = output_operator(F(2), F(2), F(2))
    right = output_operator(F(1), F(1), F(4))
    need(left == right == (F(6), F(4)), "equivalent parameter pairs")
    # p=Q=1 is a genuine equilibrium for both, with nonnegative hidden states.
    x_left = (F(1, 2), F(1, 2))
    x_right = (F(1), F(1, 4))
    need(x_left[0] >= 0 and x_left[1] >= 0, "left physical state")
    need(x_right[0] >= 0 and x_right[1] >= 0, "right physical state")
    need(F(1) - (F(2) + F(2)) * x_left[0] + F(2) * x_left[1] == 0,
         "left equilibrium first storage")
    need(F(2) * x_left[0] - F(2) * x_left[1] == 0,
         "left equilibrium second storage")
    need(F(1) - (F(1) + F(1)) * x_right[0] + F(4) * x_right[1] == 0,
         "right equilibrium first storage")
    need(F(1) * x_right[0] - F(4) * x_right[1] == 0,
         "right equilibrium second storage")
    # Deliberate failure controls.
    need(output_operator(F(2), F(2), F(3)) != left,
         "changed c must change observable coefficients")
    need(jet_zero_state(F(2), F(2), F(3), p)[2] != q3,
         "changed c must change the third jet")
    print("PASS: exact two-storage identifiability and non-identifiability checks")


if __name__ == "__main__":
    main()
