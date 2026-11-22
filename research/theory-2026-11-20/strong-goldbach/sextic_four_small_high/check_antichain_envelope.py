"""Outward same-support debit with the alternating antichain envelope."""
from fractions import Fraction as F
from hashlib import sha256
from math import comb, isqrt
from pathlib import Path


def need(ok, label):
    if not ok:
        raise ArithmeticError(label)


base = Path(__file__).with_name("check_half_envelope.py")
need(sha256(base.read_bytes()).hexdigest() ==
     "5a606be128a36b52857a2955eb2c54fcc84e2ebbf3b716c190c1899c31bf3cec",
     "different frozen half-envelope ledger")


def envelope(k):
    need(k >= 2 and k % 2 == 0, "positive even derivative")
    return F(2 * comb(k, k // 2), 2**k)


def sqrt_up(q, scale=10**12):
    a, b = q.numerator * scale**2, q.denominator
    z = isqrt(a // b)
    return F(z + (z*z*b < a), scale)


factors = list(map(F, (".859", ".661", ".563", ".501", ".456")))
for r, factor in zip((9, 11, 13, 15, 17), factors):
    ratio = F(80640, 4 * 1056 * (r - 4)**2)
    need((envelope(r-5) + ratio*envelope(r-7))/(1+ratio) < factor,
         "outward group factor")

M = [F(t)*a/2 for t, a in zip(
    (".01933", ".00345", ".000534", ".000078", ".0000114"), factors)]
U = [F(t)*a/2 for t, a in zip(
    (".373", "1.232", "12.850", "8.679", "35.095"), factors)]
mixed = sum(min(u*F(".009042"),
                sqrt_up(u*m*F(".017667")**2*F(".8")/F(".003")))
            for m, u in zip(M, U))
self_cost = sum(min(u*n, v*m) for m, u in zip(M, U) for n, v in zip(M, U))
old_low = 2*F(".1212")*sum(M)
total = 2*((F("2.446")+F(".228")+F(".007445"))*sum(M)+mixed)
total += self_cost+old_low
need(total < F(".087136"), "actual full high-exterior debit")
print(total, float(total), "< .087136 < .088")
