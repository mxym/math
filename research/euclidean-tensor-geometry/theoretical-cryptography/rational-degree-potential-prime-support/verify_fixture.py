"""Verify a fixed finite polynomial equality graph and its degree potential."""
from fractions import Fraction
from math import isqrt

x, y, z = 1000003, 1000033, 1000004507
points = (x, y, z)
weights = (1, 2, 1)
f = (271043, 13993, 0, 1)
g = (-1175780, 16694, -90, 1)
q = (0, 0, 1)
labels = ((f, q), (g, q))

def prime(p):
    return p >= 2 and all(p % k for k in range(2, isqrt(p) + 1))

def evaluate(coeff, value):
    return sum(c * value ** i for i, c in enumerate(coeff))

assert all(prime(p) for p in points)
edges = {(i, j, l) for i, p in enumerate(points)
         for j, v in enumerate(points) if i != j
         for l, (F, G) in enumerate(labels)
         if evaluate(F, p) == evaluate(G, v)}
assert edges == {(0, 2, 0), (1, 2, 1)}
# Same degree affine label added only for a separate consistency check.
extra = ((30, 1), (0, 1))
assert {(i,j) for i,p in enumerate(points) for j,v in enumerate(points)
        if i != j and evaluate(extra[0],p) == evaluate(extra[1],v)} == {(0,1)}
assert 1 - 1 + 0 == 0

R = 260
for poly in (f, g, q, *extra):
    d = len(poly) - 1
    assert poly[-1] == 1
    assert all(abs(c) <= (R // 2) ** (d - i)
               for i, c in enumerate(poly[:-1]))
    for t in (R + 1, R + 7, x, y, z):
        assert (t-R)**d <= evaluate(poly,t) <= (t+R)**d
        assert evaluate(poly,t) < evaluate(poly,t+1)
N = x * y**2 * z
L = N.bit_length()
assert N == 1000073508597992067523724369 and L == 90
assert x > 16 * 2 * L * R == 748800
lam = Fraction(3, 2)
heights = (0, 0, 1)
assert sum(e * lam**h for e,h in zip(weights,heights)) == Fraction(9, 2)
assert lam**11 <= L < lam**12
assert 2**11 * Fraction(9, 2) == 9216
u = 1000016
assert u**9 <= N**2 < (u+1)**9
assert all(abs(u-t) <= 16*L*R+1 for t in (x,y))
print("PASS: two unequal-degree edges, guarded large branch, rational lattice and exact center")
