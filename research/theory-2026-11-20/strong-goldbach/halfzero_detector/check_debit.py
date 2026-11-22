#!/usr/bin/env python3
"""Exact rational replay for the half-zero one-arm rough debit."""
from fractions import Fraction as Q
from math import factorial

def require(condition):
    if not condition:
        raise ValueError("exact inequality failed")

def upper(a):
    theta = Q(499, 1000)
    h = Q(1, 10000)
    start, end = 2*a, Q(428, 1000)
    n = (end-start)/h
    require(n.denominator == 1)
    g = lambda s: max(Q(0), 36*(1-s)**2+12*(a*a+(s-a)**2)-14)
    v = lambda s: (s/2-a)/(1-s)
    rank3 = h*sum(v(start+(i+1)*h)*g(start+i*h) for i in range(int(n)))
    rank4 = (1-4*a)**3
    rank5 = Q(4940, factorial(5)*factorial(4))*(1-5*a)**4
    require(a*a*(1-4*a) > Q(8, 1000))
    require(3 < theta/a < 4)
    b_max = Q(7, 10) + 288*(Q(1, 5)**4 -
                             (Q(3, 10)**4 - 4*Q(7, 40)**4)/12)
    require(b_max == Q(16903, 16000))
    require(-Q(78, 100)**3/64 + Q(30, 100)**3/3
            - 4*(Q(28, 100) - Q(1, 8))**3/3 < 0)
    require((Q(28, 100)/Q(78, 100))**3 <= Q(3, 64))
    require(36*(1-end)**2+12*end**2-14 < 0)
    sieve = 2/theta*(1+(theta/a-3)**2/4)
    return (rank3+rank4+rank5)*(2+b_max*sieve)

for a, cap in [(132, 969196), (140, 708596), (145, 583570)]:
    bound = upper(Q(a, 1000))
    require(bound < Q(cap, 1000000))
    print(f"floor={a/1000:.3f} upper={float(bound):.12f} cap={cap/1000000:.6f}")
