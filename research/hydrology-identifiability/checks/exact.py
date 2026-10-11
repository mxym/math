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


def parallel_moments(w1, w2, l1, l2):
    return (
        w1 + w2,
        w1 * l1 + w2 * l2,
        w1 * l1**2 + w2 * l2**2,
        w1 * l1**3 + w2 * l2**3,
    )


def three_parallel_moments(w1, w2, w3, l1, l2, l3):
    return tuple(
        w1 * l1**j + w2 * l2**j + w3 * l3**j for j in range(6)
    )


def finite_moment(weights, rates, j):
    return sum(w * l**j for w, l in zip(weights, rates))


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

    # Two active parallel reservoirs obey a second-order recurrence.  The
    # Hankel determinant is the exact non-degeneracy certificate.
    w1, w2, l1, l2 = map(F, (2, 3, 1, 4))
    m0, m1, m2, m3 = parallel_moments(w1, w2, l1, l2)
    S, P = l1 + l2, l1 * l2
    need(m2 == S * m1 - P * m0, "parallel second moment recurrence")
    need(m3 == S * m2 - P * m1, "parallel third moment recurrence")
    need(m0 * m2 - m1**2 == w1 * w2 * (l1 - l2) ** 2,
         "parallel Hankel determinant")
    need(m0 * m2 - m1**2 == F(54), "parallel exact regression value")

    # The same certificate for three parallel modes, including the cubic
    # recurrence and the 3-by-3 Hankel determinant.
    w1, w2, w3, l1, l2, l3 = map(F, (1, 2, 3, 1, 2, 4))
    n0, n1, n2, n3, n4, n5 = three_parallel_moments(
        w1, w2, w3, l1, l2, l3
    )
    e1 = l1 + l2 + l3
    e2 = l1 * l2 + l1 * l3 + l2 * l3
    e3 = l1 * l2 * l3
    need(n3 == e1 * n2 - e2 * n1 + e3 * n0,
         "three-mode third moment recurrence")
    need(n4 == e1 * n3 - e2 * n2 + e3 * n1,
         "three-mode fourth moment recurrence")
    need(n5 == e1 * n4 - e2 * n3 + e3 * n2,
         "three-mode fifth moment recurrence")
    det3 = n0 * n2 * n4 + 2 * n1 * n2 * n3 - n0 * n3**2 - n1**2 * n4 - n2**3
    need(det3 == w1 * w2 * w3 * (l1 - l2) ** 2 * (l1 - l3) ** 2 *
         (l2 - l3) ** 2, "three-mode Hankel determinant")
    need(det3 == F(216), "three-mode exact regression value")

    # Arbitrary finite spectra obey the weighted Vandermonde-square identity.
    weights = tuple(map(F, (1, 2, 3, 5)))
    rates = tuple(map(F, (1, 2, 4, 7)))
    M0 = finite_moment(weights, rates, 0)
    M1 = finite_moment(weights, rates, 1)
    M2 = finite_moment(weights, rates, 2)
    lhs = M0 * M2 - M1**2
    rhs = F(1, 2) * sum(
        wi * wj * (li - lj)**2
        for wi, li in zip(weights, rates)
        for wj, lj in zip(weights, rates)
    )
    need(lhs == rhs, "finite-spectrum Hankel variance identity")
    need(lhs > 0, "distinct positive-weight rates give strict variance")

    print("PASS: exact two-storage identifiability and non-identifiability checks")


if __name__ == "__main__":
    main()
