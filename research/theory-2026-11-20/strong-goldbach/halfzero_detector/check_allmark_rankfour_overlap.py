#!/usr/bin/env python3
"""Exact rational replay of the all-label rank-four receiver."""
from fractions import Fraction as F


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


a, c, theta = map(F, (".145", ".354", ".499"))
h = F(1, 100000)
n = int((c - a) / h)
require(a + n * h == c, "equal mesh reaches endpoint")
integral = F(0)
for j in range(n):
    u = a + j * h
    integral += h * (1 - u) ** 3 * (c - u) / (theta - u)
U4_upper = F(288, 27) * integral / (4 * c - 1)
require(U4_upper < F(".965"), "new receiver bound")

m = list(map(F, (
    ".006712176591354", ".074088", ".009809914822049",
    ".146748615358519", ".077025549076724",
)))
U = list(map(F, (
    ".058317541677312", ".965", ".353457542124065",
    ".2122213844982", ".141638207706753",
)))
p = F(".105769197972637") + F(".028817505038252")
overlap = sum(
    min(m[i] * U[j], m[j] * U[i])
    for i in range(len(m)) for j in range(len(m))
)
debit = 2 * (sum(m) - p) + overlap
require(debit < F(".602540"), "total original five-bank debit")
print(f"rank-four receiver <= {float(U4_upper):.12f} < .965")
print(f"five-bank debit <= {float(debit):.12f} < .603")
