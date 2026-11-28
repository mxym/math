#!/usr/bin/env python3
"""Pure finite checks for dyadic pentagon windows and folded root sums.

Integer/rational arithmetic certifies the congruences and four-root minima.
Separate numerical checks check the Taylor scaling on generated inputs.
The numerical checks require mpmath. No test is a substitute for the
continued-fraction or equidistribution arguments.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
from math import factorial

import mpmath as mp

mp.mp.dps = 250


def atan_inv(q, steps):
    return sum((Q((-1)**j, (2*j+1)*q**(2*j+1))
                for j in range(steps)), Q(0))


PREC = 10**45
p0 = (16*atan_inv(5, 44)-4*atan_inv(239, 44))*PREC
p0 = Q(p0.numerator//p0.denominator, PREC)
assert 3 < p0 < 4
p_err = 2*Q(1, PREC)
assert 16*Q(1, 89*5**89)+4*Q(1, 89*239**89) < Q(1, PREC)
SCALE = 10**30


def floor(q):
    return q.numerator//q.denominator


@lru_cache(None)
def cosine_bounds(j, n):
    q = p0*Q(j, n)
    term = (1+sum(((-1)**k*q**(2*k)/factorial(2*k)
                   for k in range(1, 48)), Q(0)))
    err = p_err + Q(4**96, factorial(96))
    return floor(SCALE*(term-err)), -floor(-SCALE*(term+err))


def square_coeff(signed, n):
    out = [0]*n
    for a, sa in signed:
        for b, sb in signed:
            d = (a-b) % (2*n)
            out[d % n] += sa*sb*(1 if d < n else -1)
    return out


def rotation_key(signed, n):
    E = [(a if s > 0 else a+n) for a, s in signed]
    return min(tuple(sorted((x-a) % (2*n) for x in E)) for a in E)


four_cases = four_eq = 0
for n in (4, 8, 16, 32):
    truth = ((0, 1), (1, -1), (2, -1), (3, 1))
    base = square_coeff(truth, n)
    target_key = rotation_key(truth, n)
    B = [cosine_bounds(j, n) for j in range(n)]
    for rest in combinations(range(1, n), 3):
        for signs in product((-1, 1), repeat=3):
            f = ((0, 1),)+tuple(zip(rest, signs))
            z = [u-v for u, v in zip(square_coeff(f, n), base)]
            lo = sum(a*(L if a > 0 else U) for a, (L, U) in zip(z, B))
            if any(z):
                assert lo > 0
                assert rotation_key(f, n) != target_key
            else:
                assert rotation_key(f, n) == target_key
                four_eq += 1
            four_cases += 1


# Ring arithmetic in Z[phi], with coefficient order (u,v) for u*phi+v.
def mul(t, s):
    a, b = t
    c, d = s
    return a*c+a*d+b*c, a*c+b*d


def norm(t):
    a, b = t
    return b*b+a*b-a*a


def powphi(j):
    e = (1, 0) if j >= 0 else (1, -1)
    r = (0, 1)
    j = abs(j)
    while j:
        if j & 1:
            r = mul(r, e)
        e = mul(e, e)
        j >>= 1
    return r


sqrt5 = mp.sqrt(5)
phi = (1+sqrt5)/2
conj = (1-sqrt5)/2
A = 4*mp.pi*mp.sin(mp.pi/5)/5
B = 2*mp.pi**2*(phi**3-1/phi)/125
Y0 = (5*A/B)**(mp.mpf(1)/3)
Y1 = (10*A/B)**(mp.mpf(1)/3)
Y = (Y0+Y1)/2
X = B*Y**2/A+1
lam = phi**4
period = mp.log(lam)
radix = mp.log(2)/3
C0 = B*Y0**2
magic = {}


def embeddings(t):
    u, v = t
    return u*phi+v, u*conj+v


norm_rows = leading_zeros = 0
for r in range(1, 5):
    candidates = [mul((2, -1), powphi(j)) for j in range(4)
                  if pow(3, (j-1) % 4, 5) == (-r) % 5]
    assert len(candidates) == 1
    magic[r] = candidates[0]
    for j in range(-20, 21, 4):
        t = mul(candidates[0], powphi(j))
        assert (t[0] % 5, t[1] % 5) == (-r % 5, -2*r % 5)
        assert abs(norm(t)) == 5
        norm_rows += 1
    U = int(mp.ceil((X+lam*Y)/sqrt5))
    V = int(mp.ceil(X+phi*U))
    solutions = []
    for u, v in product(range(-U, U+1), range(-V, V+1)):
        if (u % 5, v % 5) != (-r % 5, -2*r % 5):
            continue
        assert norm((u, v)) != 0 and norm((u, v)) % 5 == 0
        t, tc = embeddings((u, v))
        if t <= 0 or tc == 0:
            continue
        z = (B*tc**2/(A*t))**(mp.mpf(1)/3)
        if 1 <= z < lam and abs(tc/z) <= Y and z*t <= X:
            solutions.append(((u, v), z))
    assert len(solutions) == 1
    (u, v), z = solutions[0]
    assert abs(norm((u, v))) == 5
    t, tc = embeddings((u, v))
    assert abs(abs(tc/z)-Y0) < mp.mpf("1e-230")
    assert abs(-A*z*t+B*(tc/z)**2) < mp.mpf("1e-230")
    leading_zeros += 1

tail_rows = 0
for m in range(20, 361):
    N = 1 << m
    rho = mp.exp(m*radix)
    r = N % 5
    t0, tc0 = embeddings(magic[r])
    s0 = mp.log(B*tc0**2/(A*t0))/3
    j = int(mp.nint((s0-m*radix)/period))
    h = m*radix+j*period-s0
    u, v = mul(magic[r], powphi(4*j))
    assert (u+N) % 5 == (v+2*N) % 5 == 0
    a, b = (u+N)//5, (v+2*N)//5
    assert len({i % (N//2) for i in (0, a, -a, b, -b)}) == 5
    t, tc = embeddings((u, v))
    x, y = rho*t, tc/rho
    g = -A*x+B*y*y
    g2 = C0*(mp.exp(-2*h)-mp.exp(h))
    assert abs(g-g2) < mp.mpf("1e-150")
    alpha, beta = mp.mpf(u)/(5*N), mp.mpf(v)/(5*N)
    val = 1+2*mp.cos(2*mp.pi*(mp.mpf(1)/5+alpha))
    val += 2*mp.cos(2*mp.pi*(mp.mpf(2)/5+beta))
    rem = abs(val*rho**4-g)
    assert rem < mp.mpf("1000")/(rho*rho)
    tail_rows += 1

print("PASS: folded-four exact cases/equalities, norm/congruence, crossings, Taylor")
print(four_cases, four_eq, norm_rows, leading_zeros, tail_rows)
