"""Rational certificate for the actual cap-variant tag unions."""
from fractions import Fraction as F


def need(ok, name):
    if not ok:
        raise ArithmeticError(name)


def log_bounds(z):
    need(z >= 1, "log argument")
    t = (z - 1) / (z + 1)
    n = 96
    base = 2 * sum((t ** (2 * j + 1) / (2 * j + 1) for j in range(n)), F())
    tail = 2 * t ** (2 * n + 1) / ((2 * n + 1) * (1 - t * t))
    return base, base + tail


b, lam, rho, v = F(".4996"), F(".0001"), F(".999"), F(".498")
tag_budget = F(".0002")
k = 1 / (1 - lam)
need(b + lam + tag_budget < F(".5"), "true tagged A modulus")
need(F(".499") + tag_budget < F(".5"), "true tagged B modulus")
need(tag_budget / 3 < lam, "literal tag logs canceled by short marks")
need(v + F("1.08") * tag_budget / 3 < F(".499"), "product cap")
J0_upper = log_bounds(F(".4979") * F(".796") / (F(".204") * F(".5021")))[1]
for ratio in (F(9, 5), F(13, 10)):
    need(F(1) < F("1.02") < F("1.08") < 2 / ratio, "one/pair shifts")
    lo, hi = log_bounds(ratio)
    Dlo = (1 + lo + lo**2) / ratio - 1
    Dhi = (1 + hi + hi**2) / ratio - 1
    union = 2 * k * (rho - v) * Dlo - Dhi**2
    overlap = F(".162") * J0_upper * Dhi
    leftover = F(".162") * F(".036") - overlap
    if ratio == F(9, 5):
        need(union > F(".0687"), "large bank exact signed union")
    else:
        need(union > F(".02347"), "smaller bank exact signed union")
        need(leftover > F(".00057"), "true disjoint remaining allocation")
        need(union + leftover > F(".0239"), "no-double-spend union")
    print(f"ratio={ratio}, D>{float(Dlo):.12f}, union>{float(union):.12f}, "
          f"semiprime outside allocated lower>{float(leftover):.12f}")
