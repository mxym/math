#!/usr/bin/env python3
"""Finite checks of domination, coefficient blocks and a two-dimensional cosine envelope."""
from fractions import Fraction as F
from itertools import product
from math import cos, pi, sin
from random import Random

rng = Random(9504)
envelopes = shifts = moments = blocks = 0
for m in range(2, 5):
    for _ in range(220):
        # Three design atoms, two response atoms; each conditional row sums to 1.
        P = [[[F(a, 6), F(6-a, 6)] for _ in range(3)
              for a in [rng.randrange(7)]] for _ in range(m)]
        maxima = [[max(row[A][y] for row in P) for y in range(2)] for A in range(3)]
        masses = [sum(row) for row in maxima]
        M = sum(masses)/3
        H = max(masses)
        assert M <= H
        assert sum(sum(x/(3*M) for x in row) for row in maxima) == 1
        assert all(maxima[A][y]/M >= P[s][A][y]/M
                   for s, A, y in product(range(m), range(3), range(2)))
        for A in range(3):
            residue = 1 - masses[A]/H
            assert residue >= 0
            Qrow = [maxima[A][0]/H + residue, maxima[A][1]/H]
            assert sum(Qrow) == 1
            assert all(Qrow[y] >= P[s][A][y]/H for s, y in product(range(m), range(2)))
        if m == 2:
            V = sum(abs(P[0][A][y]-P[1][A][y])
                    for A, y in product(range(3), range(2)))/6
            assert M == 1+V
        envelopes += 1

def mul(a, b, q):
    d = len(a)
    out = [0]*d
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i+j)%d] += (-1 if i+j >= d else 1)*x*y
    return tuple(x%q for x in out)

for D in (1, 2, 4, 8):
    q = 25
    d = 2*D
    def inside(a, t):
        if t == 0:
            return all((a[i+D]-7*a[i])%q == 0 for i in range(D))
        return all(x%5 == 0 for x in a)
    for t in (0, 1):
        for _ in range(150):
            A = tuple(rng.randrange(q) for _ in range(d))
            lo = tuple(rng.randrange(q) for _ in range(D))
            J = lo+tuple(7*x%q for x in lo) if t == 0 else tuple(5*rng.randrange(5) for _ in range(d))
            assert inside(J,t)
            assert inside(mul(A,J,q),t)
            shifts += 1
        if D == 2:
            js = set()
            for lo in product(range(q), repeat=D):
                J = lo+tuple(7*x%q for x in lo) if t == 0 else tuple(5*x for z in lo for x in divmod(z,5))
                assert inside(J,t)
                js.add(J)
            assert len(js) == 625
            for j in range(d):
                assert abs(sum(cos(2*pi*a[j]/q) for a in js)) < 1e-8
                blocks += 1

# Discrete quadrature is exact for covariance on any mesh of length >=3.
for q in (3,5,9,15,25):
    N = 48
    for a,b in product(range(q),repeat=2):
        ca = [cos(2*pi*(i/N-a/q)) for i in range(N)]
        cb = [cos(2*pi*(i/N-b/q)) for i in range(N)]
        assert abs(sum(ca)) < 1e-11
        assert abs(sum(z*z for z in ca)/N-.5) < 1e-12
        assert abs(sum(x*y for x,y in zip(ca,cb))/N-.5*cos(2*pi*(a-b)/q)) < 1e-12
        moments += 1
    assert abs(min(cos(2*pi*i/q) for i in range(q))+cos(pi/q)) < 1e-12

q = 25
v,w = (4,3),(-3,4)
assert (v[1]-7*v[0])%q == (w[1]-7*w[0])%q == 0
assert sum(x*y for x,y in zip(v,w)) == 0
assert sum(x*x for x in v) == sum(x*x for x in w) == q
assert v[0]*w[1]-v[1]*w[0] == q

# Exact truncated Euler products record the sign without floating arithmetic.
prod_ratio = F(1)
for k in range(1,1001):
    a,b = F(16,(25*k)**2),F(9,(25*k)**2)
    lhs,rhs = (1-a)*(1-b),1-a-b
    assert lhs-rhs == a*b > 0 and rhs > 0
    if k <= 10:
        prod_ratio *= lhs/rhs
    blocks += 1
assert prod_ratio > 1
def sinc(z): return sin(z)/z
axis, rotated = sinc(pi/5),sinc(4*pi/25)*sinc(3*pi/25)
assert .0003 < rotated-axis < .0005
N=192
quad = sum(cos(2*pi*((4*(i+.5)/N-3*(j+.5)/N)-.5)/25)
           for i,j in product(range(N),repeat=2))/(N*N)
assert abs(quad-rotated)<1e-5

print("PASS finite envelopes / ideal translates / trigonometric moments / block certificates:",
      envelopes,shifts,moments,blocks)
