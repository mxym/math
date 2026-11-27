#!/usr/bin/env python3
"""Rational certificates for a first-zero constant and a hexagonal lift bound."""
from fractions import Fraction as F
from itertools import product
from math import factorial


def atan_interval(x, n):
    s = sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n))
    next_term = (-1)**n*x**(2*n+1)/(2*n+1)
    return sorted((s, s+next_term))


def pi_interval():
    a, b = atan_interval(F(1, 5), 20)
    c, d = atan_interval(F(1, 239), 10)
    # Machin's identity, obtained from the tangent addition formula.
    lower, upper = 16*a-4*d, 16*b-4*c
    den = 10**20
    L, H = F(314159265358979323846, den), F(314159265358979323847, den)
    assert L < lower <= upper < H
    return L, H


def integral_interval(alpha):
    # Change x=3y/4. The positive factor 3/4 is omitted; this gives
    # the sign of the integral. Evaluate a product of Taylor polynomials.
    lp, hp = pi_interval()
    p = (lp+hp)/2
    a, c = F(9, 32)*alpha, F(3, 2)*p
    N, M = 32, 30
    E = [(-a)**k/factorial(k) for k in range(N+1)]
    C = [(-1)**l*c**(2*l)/factorial(2*l) for l in range(M+1)]
    mid = sum(E[k]*C[l]/(2*k+2*l+1)
              for k in range(N+1) for l in range(M+1))
    err_exp = a**(N+1)/factorial(N+1)
    err_cos = c**(2*M+1)/factorial(2*M+1)
    err_pi = F(3, 4)*(hp-lp)
    error = err_exp+(1+err_exp)*err_cos+err_pi
    return mid-error, mid+error


def hex_shells():
    # k+1/3=Q(m+1/3,n+1/3)>=3/4*max((m+1/3)^2,(n+1/3)^2),
    # so the displayed box contains the whole range k<=3.
    shells = [set() for _ in range(4)]
    for m, n in product(range(-3, 4), repeat=2):
        k = m*m+n*n+m*n+m+n
        assert k >= 0
        if k < 4:
            shells[k].add((3*m+1, 3*n+1))
    assert list(map(len, shells)) == [3, 3, 6, 0]
    assert shells[0] == {(1, 1), (-2, 1), (1, -2)}
    assert shells[1] == {(-2, -2), (4, -2), (-2, 4)}
    pts = shells[1] | {(-a,-b) for a,b in shells[1]}
    wanted = {(3,0),(-3,0),(0,3),(0,-3),(3,-3),(-3,3)}
    pairs = {(a,b) for a,b in product(pts, pts)
             if a<b and a[0]+b[0] == 2*((a[0]+b[0])//2)
             and a[1]+b[1] == 2*((a[1]+b[1])//2)
             and ((a[0]+b[0])//2,(a[1]+b[1])//2) in wanted}
    assert {((a[0]+b[0])//2,(a[1]+b[1])//2) for a,b in pairs} == wanted
    assert len(pairs) == 6 and all(sum(x in pair for pair in pairs)==2 for x in pts)


def hex_bound():
    z = F(28, 25)
    T = sum(z**k/factorial(k) for k in range(9))
    tail = z**9/factorial(9)/(1-z/10)
    qlo, qhi = F(3262, 10000), F(3263, 10000)
    assert 1/qhi < T and T+tail < 1/qlo
    w = qhi**3
    delta_bound = qhi*(3+3*w+6*w*w+9*w**4*(5/(1-w)+w/(1-w)**2))-1
    assert delta_bound < F(3, 2)*qlo**4
    assert delta_bound < F(153, 10000)
    assert F(169, 10000) < F(3, 2)*qlo**4


if __name__ == "__main__":
    lo, hi = F(594378, 100000), F(594379, 100000)
    assert integral_interval(lo)[1] < 0
    assert integral_interval(hi)[0] > 0
    hex_shells()
    hex_bound()
    print("PASS: exact first-zero bracket 5.94378 < A_z < 5.94379; "
          "shifted shell counts 3,3,6,0; all six hexagon midpoints and curvature 5.04 bound")
