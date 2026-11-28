#!/usr/bin/env python3
"""Deterministic small-range checks for the triprime endpoint identities."""

from decimal import Decimal, getcontext
from itertools import combinations

getcontext().prec = 90
TOL = Decimal("1e-55")


def primes_upto(n):
    out = []
    for k in range(2, n + 1):
        if all(k % p for p in out if p * p <= k):
            out.append(k)
    return out


def cbrt(n):
    lo, hi = Decimal(1), Decimal(n)
    for _ in range(340):
        mid = (lo + hi) / 2
        if mid * mid * mid < n:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def F(t, n):
    return (t - 1) ** 2 * (Decimal(n) / (t * t) - 1)


def G(t, n):
    return 2 * t + Decimal(n) / (t * t)


def endpoints(n, tot):
    u = cbrt(n)
    lo, hi = Decimal(1), u
    for _ in range(340):
        mid = (lo + hi) / 2
        if F(mid, n) < tot:
            lo = mid
        else:
            hi = mid
    sm = (lo + hi) / 2

    lo, hi = u, Decimal(n).sqrt()
    for _ in range(340):
        mid = (lo + hi) / 2
        if F(mid, n) > tot:
            lo = mid
        else:
            hi = mid
    return sm, (lo + hi) / 2


def require(ok, msg):
    if not ok:
        raise AssertionError(msg)


ps = primes_upto(73)[:20]
count = 0
for x, y, z in combinations(ps, 3):
    n = x * y * z
    tot = (x - 1) * (y - 1) * (z - 1)
    e1 = x + y + z
    e2 = x * y + x * z + y * z

    require(tot == n - e2 + e1 - 1, "symmetric relation")
    for p in (x, y, z):
        require(p**3 - e1 * p**2 + e2 * p - n == 0, "cubic root")

    sm, sp = endpoints(n, tot)
    u = cbrt(n)
    require(Decimal(1) < sm < u < sp < Decimal(n).sqrt(),
            "root branches")

    dx = (Decimal(y).sqrt() - Decimal(x).sqrt()) ** 2
    dz = (Decimal(z).sqrt() - Decimal(y).sqrt()) ** 2
    rb = dx * Decimal(z - x) / Decimal(x - 1)
    rt = dz * Decimal(z - x) / Decimal(z - 1)
    cb, ct = G(sm, n), G(sp, n)

    require(ct - TOL <= e1 <= ct + rt + TOL,
            "upper endpoint interval")
    require(cb - rb - TOL <= e1 <= cb + TOL,
            "lower endpoint interval")

    rtop = Decimal(y * z).sqrt()
    rbot = Decimal(x * y).sqrt()
    require(abs((F(rtop, n) - tot) - Decimal(x - 1) * dz) < TOL,
            "top F identity")
    require(abs((Decimal(e1) - G(rtop, n)) - dz) < TOL,
            "top G identity")
    require(abs((F(rbot, n) - tot) - Decimal(z - 1) * dx) < TOL,
            "bottom F identity")
    require(abs((Decimal(e1) - G(rbot, n)) - dx) < TOL,
            "bottom G identity")
    count += 1

require(count == 1140, "coverage count")
print("clustered triprime totient checker")
print(f"triples_checked = {count}")
print("identities = PASS")
print("endpoint_intervals = PASS")
print("cubic_coefficients = PASS")
print("standard_library_only = PASS")
