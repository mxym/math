#!/usr/bin/env python3
"""Exact coefficient and scalar-inequality regression certificates."""
from fractions import Fraction as R
from itertools import product


def add(a, b):
    return tuple((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b))))


def scale(a, c):
    return tuple(c * z for z in a)


def mul(a, b):
    p = [0] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            p[i+j] += x*y
    return tuple(p)


# All polynomials here are represented by their coefficients in w.
w, den, la_num, al = (0, 1), (1, -1), (2, -4), (1, -3)
den2 = mul(den, den)
c_num = (0, 0, 4)
b_num = mul(la_num, al)
K_num = add(add(b_num, den2), scale(c_num, -1))
assert K_num == mul((3, -9), den)
C_num = add(add(K_num, den2), scale(c_num, -1))
assert C_num == mul((4, -2), (1, -3))
F_num = add(c_num, mul(w, add(add(K_num, mul(la_num, den)), scale(c_num, -1))))
assert F_num == mul((0, 5, -9), den)
lhs = add(mul(mul(scale(w, 4), den), den2), scale(mul((0, 5, -9), (0, 5, -9)), -1))
rhs = mul(mul(w, (1, -5)), (4, -17, 17))
assert lhs == rhs
assert 17*R(1, 5)**2-17*R(1, 5)+4 == R(32, 25)
print("coefficient identities: K, C_*, F, and ideal squared gap PASS")

n = 0
for la, u, t in product((R(101, 100), R(3, 2), R(2), R(7)),
                        (R(0), R(1, 12), R(1, 3), R(4, 7)),
                        (R(0), R(1, 20), R(1, 3), R(4, 7), R(10))):
    v = la-1
    h = lambda z: la*z/(v+la*z)
    b = la*v/(v+la*u)**2
    c = h(u)**2
    gap = c+b*t-h(t)
    assert gap == v*la**2*(t-u)**2/((v+la*u)**2*(v+la*t))
    assert 0 <= max(R(0), h(t)-c) <= b*t
    n += 1
print(f"exact scalar tangency regressions: {n} PASS")

for ww, d, y, target_gap in (
        (R(19, 100), R(39, 50), R(1, 300), R(209383, 590490000)),
        (R(199, 1000), R(399, 500), R(1, 5000), R(1632220601, 5346675000000))):
    ff = ww*(5-9*ww)/(1-ww)
    cc = (2*ww/(1-ww))**2
    uu = 2*(2-ww)*(1-3*ww)/(1-ww)**2
    assert 0 < y <= 1 and 0 < d <= 1
    assert d*d < 4*ww*(1-ww)
    gap = d-ff-uu*y-(1-cc)*y*y
    assert gap == target_gap > 0
    print(f"w={ww}: D>={d} certifies e>{y*y}; exact gap={gap} PASS")
