"""Exact finite checks for the adaptive whole-low collision (run also with -O)."""
from fractions import Fraction as Q
from itertools import product


def require(test, message):
    if not test:
        raise ArithmeticError(message)


D_MIN = Q(499, 1000)
ALPHA = Q(31, 200)
DELTA_MAX = Q(1, 1000)
SIGMA_MIN, SIGMA_MAX = Q(1, 10), Q(14, 100)

# All fixed-cut profiles are uniformly away from the alpha and relative-shape gates.
require(Q(1, 2) - SIGMA_MAX > ALPHA, "small eligible factor")
last_u = Q(1, 2) - 2 * DELTA_MAX
first_l = Q(1, 2) - SIGMA_MIN + 2 * DELTA_MAX
floor_lambda = 2 * (last_u - first_l) / (last_u + first_l)
require(floor_lambda > Q(21, 100), "reference ratio")
require(1 / (Q(245, 1000) * (1 - SIGMA_MAX)) < Q(48, 10), "upper sieve factor")
require(Q(1, 5) / Q(48, 10) == Q(1, 24), "paired cost scale")
require((2 * Q(63 - 43, 63 + 43)) / 12 > Q(31, 1000), "dyadic lower")


def marker_divisors(labels, delta):
    limit = Q(1, 2) - delta
    hi_score, low_divisors = 0, []
    for bits in product((0, 1), repeat=len(labels)):
        subset = tuple(a for a, bit in zip(labels, bits) if bit)
        if sum(subset) > limit:
            continue
        if any(a < ALPHA for a in subset):
            low_divisors.append(subset)
        else:
            hi_score += (-1) ** len(subset)
    return hi_score, low_divisors


profiles = 0
for d in (Q(1, 10000), Q(1, 2000), Q(1, 1000)):
    for j in range(100, 141):
        s = Q(j, 1000)
        require(marker_divisors((s, 1 - s), d) == (1, [(s,)]), "rank two")
        for k in range(1, 21):
            p_lo, p_hi = 1 / Q(2) - s + 2 * d, 1 / Q(2) - 2 * d
            p = p_lo + (p_hi - p_lo) * Q(k, 21)
            q = 1 - s - p
            require(p_lo < p < p_hi and p_lo < q < p_hi, "balanced gates")
            require(marker_divisors((s, p, q), d) == (-1, [(s,)]), "rank three")
            profiles += 1

cases = 0
for X, Y in product((Q(i, 4) for i in range(25)), repeat=2):
    for j in range(-28, 29):
        t = Q(j, 7)
        rhs = X * max(0, 1 + t) + Y * max(0, 1 - t)
        require(rhs >= 2 * min(X, Y), "optimal physical positive part")
        cases += 1
print(f"certified constants; {profiles} rational profiles and {cases} sign allocations")
