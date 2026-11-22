"""Rational sign and size checks for WideNoHighRankTaggedCross."""
from fractions import Fraction as Q


def need(x, name):
    if not x:
        raise ArithmeticError(name)


def log_bounds(x):
    need(1 <= x, "rational logarithm input")
    e = 0
    while x > 2:
        e += 1
        x /= 2

    def core(v):
        z = (v - 1) / (v + 1)
        lo = 2 * sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(24)), Q(0))
        return lo, lo + 2 * z**49 / (49 * (1 - z * z))

    lo, hi = core(x)
    a, b = core(Q(2))
    return lo + e * a, hi + e * b


q0, q1 = Q(".5022"), Q(".5086")
a = Q(".014")
p1a, p1b, p2a, p2b = map(Q, (".00105", ".00120", ".00140", ".00160"))
b, w, lam = Q(".490"), Q(".499"), Q(".006")
k = 1 / (1 - lam)

need((56*q1 - 17)/23 < Q(".4996") < Q(".5"), "two dispersion pieces")
need(b + lam + p1b + p2b < Q(".4996"), "actual short A modulus")
need(w + p1b + p2b < q0, "actual tagged B rail")
need(1 - q0 < Q(".4985"), "physical cap on all other marks")
need(1 - q0 - a <= Q(".486") and 1 - q1 > b, "only full divisor outside affine plateau")
need(35 <= (1 - q0)/a < 36, "finite cofactor ranks")
need(p1a > Q(".001") and p2a > p1b and p2b < lam, "distinct physical tag banks")
need(lam+p1b+p2b < Q(".4985"), "shifted lower cap endpoint")
need(Q(".498")+min(p1a,p2a) > w, "shifted upper cap endpoint")

u0, u1 = (1 - q1)/a, (1 - q0)/a
need(log_bounds(u0-1)[0] > Q("3.5"), "I2 lower")
need(log_bounds(u1-1)[1] < Q("3.56"), "I2 upper")
need(1/(u0-1) < Q(".03"), "one Dickman integral bound")
need(log_bounds(3*u0/4)[0] > Q("3.25"), "I3 lower endpoint")
need(log_bounds(Q(6))[1] < Q("1.80"), "I3 upper endpoint")
j3 = (Q("3.25")**2 - Q("1.80")**2)/2
need(j3 > Q("3.66"), "I3 integral lower")
need(3 * a < (1-q1) / 4, "whole displayed I3 subinterval is nonempty")
need(1+k*(1-q1)>Q("1.49") and 1/(1-q0)>2, "fixed geometry")
need(1 - k*Q(".001") > Q(".9989"), "same cap calibration")
need(p1b/p1a == p2b/p2a == Q(8,7), "reciprocal bank widths")
need(log_bounds(Q(8,7))[0] > Q(".133"), "width lower")

common = Q(".9989")*Q(".133")**2*(q1-q0)*Q("1.49")*2
claims = [
    ("rank >= 3 negative", common*Q(".97"), Q(".00032")),
    ("rank >= 4 positive", common*Q("2.5"), Q(".00083")),
    ("exact rank 3 negative", common*Q("3.5"), Q(".00117")),
    ("rank >= 5 negative", common*Q("1.07"), Q(".00035")),
]
for name, lower, target in claims:
    need(lower > target, name)
    print(f"{name}: |coefficient| > {float(lower):.12f}")
