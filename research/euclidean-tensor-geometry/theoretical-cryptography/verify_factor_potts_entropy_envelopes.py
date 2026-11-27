#!/usr/bin/env python3
"""Exact derivative checks and rational log enclosures for the Potts envelopes."""
from fractions import Fraction as F
from functools import lru_cache

checks = 0


def ok(x):
    global checks
    checks += 1
    if not x:
        raise AssertionError("exact check failed")


def I(x):
    return F(x), F(x)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def neg(x):
    return -x[1], -x[0]


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    p = [a*b for a in x for b in y]
    return min(p), max(p)


def div(x, y):
    ok(y[0]*y[1] > 0)
    return mul(x, (1/y[1], 1/y[0]))


def scale(x, k):
    return mul(x, I(k))


def logseries(x):
    # x in [1,2]: use the odd power expansion, enclosing its positive tail.
    z = (x-1)/(x+1)
    S, power = F(0), z
    n = 25
    for k in range(n):
        S += 2*power/(2*k+1)
        power *= z*z
    tail = 2*power/((2*n+1)*(1-z*z))
    return S, S+tail


LOG2 = logseries(F(2))


@lru_cache(None)
def log(x):
    x = F(x)
    if x <= 0:
        raise AssertionError("invalid log argument")
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x >= 2:
        x /= 2
        k += 1
    return add(logseries(x), scale(LOG2, k))


def H(p):
    h = I(0)
    for y in p:
        if y:
            h = sub(h, scale(log(y), y))
    return h


def D(q, t):
    p = [(1+(q-1)*t)/q] + [(1-t)/q]*(q-1)
    return sub(log(F(q)), H(p))


def ell(a, t):
    return log((1+a*t)/(1-t))


def poly(a, t):
    return (1+a*t)*(1-t)


def dpoly(a, t):
    return a-1-2*a*t


def bracket(a, L, t):
    return a-1-2*a*(1+L)*t-a*(a-1)*L*t*t


def tangent_sign(q, L, t):
    a = q-1
    R = scale(div(ell(a, L*t), ell(a, t)), L)
    return sub(mul(D(q, t), R), D(q, L*t))


def deriv(q, L):
    a = q-1
    vals = [F(k, 20) for k in range(21)]
    for t in vals[1:-1]:
        left = (dpoly(a, t)*poly(a, L*t)
                - L*poly(a, t)*dpoly(a, L*t))
        ok(left == (1-L)*bracket(a, L, t))
    if L == -F(1, a):
        for t in vals:
            ok(bracket(a, L, t) == (a-1)*(1-t)**2)
        # Endpoint exponent gamma is >1.
        ok(sub(log(F(q)), scale(log(F(q, a)), a))[0] > 0)
    else:
        values = [bracket(a, L, t) for t in vals]
        ok(values[0] > 0 and values[-1] < 0)
        ok(all(x > y for x, y in zip(values, values[1:])))
        ok(any(tangent_sign(q, L, F(1, 2**k))[0] > 0
               for k in range(3, 15)))
        ok(any(tangent_sign(q, L, 1-F(1, 2**k))[1] < 0
               for k in range(3, 24)))


def output(p, L):
    q = len(p)
    return [L * x + (1-L)/q for x in p]


def polygon(q, L):
    xs = [log(F(k)) for k in range(1, q+1)]
    ys = [H(output([F(1, k)] * k + [F(0)] * (q-k), L))
          for k in range(1, q+1)]
    for i in range(q-2):
        prev_x, next_x = sub(xs[i+1], xs[i]), sub(xs[i+2], xs[i+1])
        prev_y, next_y = sub(ys[i+1], ys[i]), sub(ys[i+2], ys[i+1])
        ok(sub(mul(prev_y, next_x), mul(next_y, prev_x))[0] > 0)
    for k in range(2, q+1):
        dx, dy = sub(xs[k-1], xs[k-2]), sub(ys[k-1], ys[k-2])
        M = L+k*(1-L)/q
        r = L/M
        ok(-F(1, k-1) <= r < 1)
        for j in [1, 3, 7, 9]:
            p = [F(j,10*k)] + [F(10*k-j,10*k*(k-1))]*(k-1) + [F(0)]*(q-k)
            hx, hy = H(p), H(output(p, L))
            gap = sub(mul(sub(hx, xs[k-2]), dy), mul(sub(hy, ys[k-2]), dx))
            t = -F(10-j, 10*(k-1))
            if k == 2 and L == -F(1, q-1):
                ok(bracket(k-1,r,t) == 0)
                ok(gap[0] <= 0 <= gap[1])
            else:
                ok(bracket(k-1,r,t) > 0)
                ok(gap[0] > 0)


def main():
    for q in range(3, 10):
        a = q-1
        for L in [-F(1,a), -F(7,8*a), -F(1,2*a), F(1,9), F(1,2), F(4,5)]:
            deriv(q, L)
            polygon(q, L)
    print(f"Potts envelope checks passed: {checks} certified rational inequalities.")


if __name__ == "__main__":
    main()
