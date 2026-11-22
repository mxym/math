#!/usr/bin/env python3
"""Exact rational replay of the all-label rank-four and rank-five prices."""
from fractions import Fraction as F
from collections import Counter
from math import factorial, prod


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

def rank_five_mass():
    # Ordered simplex, with a = 37120/256000 and exact angular
    # mesh 275/256000. All quantities in the inner loop are integers.
    D, A, step = 256000, 37120, 275
    D2, D4 = D**2, D**4
    den = 4 * D**3
    scale = 10**15
    mult = scale * step**4

    def P(q):
        z = D - 2*q
        return z*z*(7*D2 - 3*z*z)

    # All endpoints are multiples of 5 in [0,D].
    Ptab = {q: P(q) for q in range(A, D+1, 5)}
    stab = {q: (P(q) if 2*q <= D else -P(q))
            for q in range(0, D+1, 5)}
    nbox, upper = 0, 0
    for i in range(256//5 + 1):
        u = A + i*step
        for j in range(i, (256-i)//4 + 1):
            v = A + j*step
            uv = stab[u+v+2*step]
            for k in range(j, (256-i-j)//3 + 1):
                w = A + k*step
                base = uv + stab[u+w+2*step] + stab[v+w+2*step]
                for ell in range(k, (256-i-j-k)//2 + 1):
                    z = A + ell*step
                    t = u+v+w+z
                    fifth = max(z, D-t-4*step)
                    nbox += 1
                    top = (-4*D4 + Ptab[u] + Ptab[v] + Ptab[w]
                           + Ptab[z] + Ptab[fifth] - base
                           - stab[u+z+2*step] - stab[v+z+2*step]
                           - stab[w+z+2*step] - stab[D-t+u]
                           - stab[D-t+v] - stab[D-t+w] - stab[D-t+z])
                    if top > 0:
                        ties = prod(factorial(r) for r in Counter(
                            (i, j, k, ell)).values())
                        bottom = den*u*v*w*z*fifth*ties
                        upper += (top*mult+bottom-1)//bottom
    require((nbox, upper) == (1_673_243, 6_124_352_113_757),
            "rank-five integer upper replay")
    return F(upper, scale)


m5_upper = rank_five_mass()
require(m5_upper < F(".006125"), "new rank-five mass bound")

m = list(map(F, (
    ".006712176591354", ".074088", ".006125",
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
require(debit < F(".583718"), "total original five-bank debit")
print(f"rank-four receiver <= {float(U4_upper):.12f} < .965")
print(f"rank-five mass <= {float(m5_upper):.15f} < .006125")
print(f"five-bank debit <= {float(debit):.12f} < .584")
