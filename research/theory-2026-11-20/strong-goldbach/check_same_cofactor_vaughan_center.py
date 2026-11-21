"""Rational calibration and finite arithmetic checks (works with python -O)."""
from fractions import Fraction as Q
from itertools import product


def require(test, message):
    if not test:
        raise ArithmeticError(message)


def log_interval(r):
    y = (r - 1) / (r + 1)
    require(0 <= y < 1, "log input")
    n = 8
    low = 2 * sum((y ** (2 * k + 1) / (2 * k + 1) for k in range(n)), Q(0))
    return low, low + 2 * y ** (2 * n + 1) / ((2 * n + 1) * (1 - y*y))


def j_interval(delta, mesh=12000):
    start, stop = Q(1, 10), Q(7, 50)
    step = (stop - start) / mesh
    scale = 10**12
    lower = upper = 0
    a = start
    lo_a, hi_a = log_interval((Q(1, 2) - 2*delta)/(Q(1, 2) - a + 2*delta))
    for _ in range(mesh):
        b = a + step
        lo_b, hi_b = log_interval((Q(1, 2) - 2*delta)/(Q(1, 2) - b + 2*delta))
        fa, fb = (1-2*a)**3, (1-2*b)**3
        lo_n = (1-fa)-(1+fa)*hi_b
        hi_n = (1-fb)-(1+fb)*lo_a
        da, db = a*(1-a), b*(1-b)
        lo = min(lo_n/da, lo_n/db)
        hi = max(hi_n/da, hi_n/db)
        lower += (scale*lo)//1
        upper -= (-scale*hi)//1
        a, lo_a, hi_a = b, lo_b, hi_b
    return Q(lower, scale)*step, Q(upper, scale)*step


lo, hi = j_interval(Q(0))
require(Q(6282, 100000) < lo < hi < Q(6284, 100000), "J0 integral")
require(Q(6941, 100000) < lo+Q(659, 100000) < hi+Q(659, 100000) < Q(6943, 100000), "threshold")
print("J0:", float(lo), float(hi))
lo, hi = j_interval(Q(1, 1000))
require(Q(6791, 100000) < lo < hi < Q(6794, 100000), "J_.001 integral")
print("J_.001:", float(lo), float(hi))
require(Q(49, 100)*Q(86, 100) - Q(2, 5) == Q(107, 5000), "BV reserve")

# Local inverse Euler exactly cancels the masked signed p-bit; φ(d p^j) correction.
for p, j, k in product((3, 5, 7, 11, 13), range(1, 12), range(5)):
    inverse_coeff = Q(1, (p-1)**j)
    lower_coeff = Q(1, (p-1)**(j-1))
    require(inverse_coeff - lower_coeff/(p-1) == 0, "inverse Euler")
    # Direct local formula avoids enumerating p^(j+k) integers at large powers.
    phi_d = 16 * (p**(k-1)*(p-1) if k else 1)
    phi_l = p**(j-1)*(p-1)
    phi_dl = 16*p**(j+k-1)*(p-1)
    require(Q(1, phi_dl) == (Q(p-1, p) if k else 1)*Q(1, phi_d*phi_l), "Euler overlap")

# Vaughan coefficient identity on all small factorizations, with formal log of a prime power.
def divs(n):
    return [d for d in range(1,n+1) if n % d == 0]


def fac(n):
    out = {}
    p = 2
    while p*p <= n:
        while n%p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def mu(n):
    d = fac(n)
    return 0 if max(d.values(), default=0)>1 else (-1)**len(d)


def mang(n, p):
    f = fac(n)
    return int(list(f) == [p] and len(f) == 1)

for n, U, V in product(range(2, 105), (2, 3, 5, 9), (3, 7, 12)):
    for p in fac(n):
        exact = mang(n,p)
        first = exact * (n<=V)
        t1 = sum(mu(d)*fac(n//d).get(p,0) for d in divs(n) if d<=U)
        t2 = sum(mu(d)*mang(l,p) for d in divs(n) if d<=U for l in divs(n//d) if l<=V)
        t3 = sum(mu(d)*mang(l,p) for d in divs(n) if d>U for l in divs(n//d) if l>V)
        require(exact == first+t1-t2+t3, "Vaughan identity")
print("certified BV gap, finite Vaughan and local Euler identities")
