#!/usr/bin/env python3
"""Exact Gaussian-integer replay of the Eq. (C.46) witness."""

UNITS = [1, 3, 9, 7]  # successive powers of 3 modulo 10
I_POWERS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def conj(a):
    return (a[0], -a[1])


def add(values):
    return (sum(v[0] for v in values), sum(v[1] for v in values))


def chi(k, x):
    exponent = UNITS.index(x % 10)
    return I_POWERS[(k * exponent) % 4]


n1, n2, ell = 1, 7, 3
target = int((n1 - ell * n2) % 10 == 0)

printed_num = add([
    mul(mul(conj(chi(k, ell)), chi(k, n1)), chi(k, n2))
    for k in range(4)
])
corrected_num = add([
    mul(mul(conj(chi(k, ell)), chi(k, n1)), conj(chi(k, n2)))
    for k in range(4)
])

print(f"target indicator: {target}")
print(f"printed numerator: {printed_num} / 4")
print(f"corrected numerator: {corrected_num} / 4")

assert target == 1
assert printed_num == (0, 0)
assert corrected_num == (4, 0)
print("PASS: printed Eq. (C.46) fails on the exact witness")
print("PASS: conjugating the second transform repairs the identity")
