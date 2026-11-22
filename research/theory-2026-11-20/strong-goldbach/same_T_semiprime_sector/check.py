"""Exact rational certificate for the same-T semiprime sector."""
from fractions import Fraction as Q


def need(ok, label):
    if not ok:
        raise ArithmeticError(label)


def log_box(x):
    need(x >= 1, "positive log ratio")
    t = (x - 1) / (x + 1)
    n = 96
    partial = 2 * sum((t ** (2 * j + 1) / (2 * j + 1) for j in range(n)), Q())
    tail = 2 * t ** (2 * n + 1) / ((2 * n + 1) * (1 - t * t))
    return partial, partial + tail


a, g = Q("0.204"), Q("0.4979")
lam, rho = Q("0.0001"), Q("0.999")
b, aff = Q("0.4996"), Q("0.4992")
v, w = Q("0.498"), Q("0.499")
unit_end = Q("0.4985")
delta = 1 - rho
D = b + lam - delta
k = 1 / (1 - lam)
need(0 < lam < a < g < v < unit_end < w < Q(1, 2), "physical mark caps")
need(b < 1 - g and g < aff < b and b + lam < Q(1, 2), "full source affine arguments and BV")
need(rho > 1 - a and delta < v and delta < aff and rho > b, "same no-high partition")
need(2 * delta < D and delta < a and rho > (b + lam) / 2, "genuine sieve primes and size-separated units")
j0_upper = log_box(g * (1 - a) / (a * (1 - g)))[1]
raw_lower = Q(".755") - Q(".01") - Q("3.446") * log_box((1 - g) / g)[1]
b_debit = k * (v - lam) * j0_upper
e_debit = 2 * k * delta * j0_upper / D
gap = raw_lower - b_debit - e_debit
need(raw_lower > Q(".7160"), "retained genuine semiprime anchor")
need(b_debit < Q(".6738") and e_debit < Q(".0055"), "two simultaneous real debits")
need(gap > Q(".036"), "same-score signed sector")
need(a * (1 - a) > Q(".162"), "true source lower factor")
need(Q(".162") * Q(".036") > Q(".0058"), "positive full actual sector")
need(Q(".162") * Q(".035") > Q(".0056"), "positive finite-rank actual sector")
print(f"raw > {float(raw_lower):.12f}, J0 < {float(j0_upper):.12f}")
print(f"B debit < {float(b_debit):.12f}, E debit < {float(e_debit):.12f}, signed gap > {float(gap):.12f}")
