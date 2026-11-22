#!/usr/bin/env python3
"""Exact constants for BilateralRoughDebit.md (no sampled prime data)."""
from fractions import Fraction as Q

def need(test, label):
    if not test:
        raise SystemExit("failed: " + label)

v, D = Q(498, 1000), Q(49, 100)
w = 1 - 2*v
# I2 = 2 artanh(w); for j>=1, 1/(2*j+1)<=1/3.
I2_upper = 2*(w + w**3/(3*(1-w*w)))

for a, cap in ((Q(145, 1000), Q(933, 1000)), (Q(15, 100), Q(645, 1000))):
    need(7*a > 1 and 6*a < 1, "rank stops at six")
    need(2*v + a > 1, "exceptional pairs intersect")
    need(1-v-a < v and 1-4*a < v and 4*a > Q(4996,10000),
         "rank-three/four/six support")
    need(v > 2*a and 1-v > 3*a and Q(4996,10000)<1-v,
         "denominators and supports")
    s = D/a
    need(3 < s < 5, "linear-sieve function")
    d = 1-5*a
    c = d/a
    I4 = w*(1-v-3*a)**2/(12*v*a*a*(v-2*a))
    I4ex = w**3/(48*a**4)
    I5 = d**4/(2880*a**5)*(Q(5,6)/(1+c+Q(2,5)*c*c)+Q(1,6)/(1+c))
    I6 = Q(10,720)*w*(1-v-3*a)**4/(4*a**4*(v-2*a)**2)
    P = I2_upper+I4+6*I5+I6
    A = (2/D)*(1+(s-3)**2/4)
    debit = 2*A*(2*P+10*I4ex)
    need(debit < cap, "strict debit bound")
    print(f"a={float(a):.3f}, rational upper displayed as {float(debit):.12f}, cap {float(cap):.3f}")
