"""Exact rational certificate for the stronger anchor and moved wide cutoff."""
from fractions import Fraction as Q


def need(condition, label):
    if not condition:
        raise ArithmeticError(label)


def log_box(x):
    need(x >= 1, "log input")
    e = x.numerator.bit_length() - x.denominator.bit_length()
    if Q(2) ** e > x:
        e -= 1

    def unit_box(v):
        t = (v - 1) / (v + 1)
        n = 18
        partial = 2 * sum((t ** (2 * j + 1) / (2 * j + 1) for j in range(n)), Q())
        tail = 2 * t ** (2 * n + 1) / ((2 * n + 1) * (1 - t * t))
        den = 10 ** 17
        return Q(partial * den // 1, den), Q(-(-(partial + tail) * den // 1), den)

    lo, hi = unit_box(x / Q(2) ** e)
    l2, u2 = unit_box(Q(2))
    return lo + e * l2, hi + e * u2


a = Q(204, 1000)
a0 = Q(252, 1000)
theta = Q(7, 32)
height = Q(100001, 100000)
s0 = Q(5, 100000)
tm = (1 - height * theta) / 4
A = 1 - height * theta / 2 - s0
B = Q(5, 2)
need(Q(1, 5) < a < Q(1, 4) < a0 < Q(254, 1000), "true ranks and original packed range")
need(tm < a and (A - B * a) / 3 < a and A > B * a0, "same residual sieve branch")
need(2 * a0 < A - Q(3, 2) * a0, "first forced square test")

h_gain = 2 / A * log_box(a0 * (A - B * a) / (a * (A - B * a0)))[0]
steps = 8192
dx = (a0 - a) / steps
den = 10 ** 18
i3_gain = 0
for i in range(steps):
    t = a + i * dx
    cell = dx * log_box((1 - 2 * t) / t)[1] / (t * (1 - t))
    i3_gain += Q(-(-cell * den // 1), den)
i4 = (1 - 4 * a) ** 3 / (144 * a ** 3 * (1 - 3 * a))
K = Q(3446, 1000)
anchor = Q(3001, 10000) + h_gain - K * (i3_gain + i4)
need(anchor > Q(755, 1000), "new rough anchor")

rho = Q(542, 1000)
g = Q(457, 1000)
affine_end = Q(4584, 10000)
b = Q(4588, 10000)
tau = Q(40, 1000)
lam_max = Q(1, 1000)
need(rho > Q(1, 2) and g + rho < 1 and 1 - rho < affine_end < b, "true high mark and affine regions")
need(tau + b < Q(1, 2) and lam_max + b < Q(1, 2), "sub-root and whole calibration rails")
raw = Q(755, 1000) - Q(1, 100) - K * log_box((1 - g) / g)[1]
weighted = a * (1 - a) * raw
debit = (1 - rho) * tau / (1 - lam_max) ** 2
stripe = 2 * (tau - lam_max) * (rho - lam_max) - (tau - lam_max) ** 2
need(raw > Q(1508, 10000), "actual high source raw reserve")
need(weighted > Q(244, 10000), "actual high source weighted reserve")
need(debit < Q(184, 10000), "paid conditional debit")
need(weighted - debit > Q(6, 1000), "conditional residual gap")
need(stripe > Q(406, 10000), "positive low-low strip")
print(f"certified new anchor > {float(anchor):.10f}")
print(f"high reserve > {float(raw):.10f}, weighted > {float(weighted):.10f}")
print(f"conditional debit <= {float(debit):.10f}, gap > {float(weighted-debit):.10f}")
print(f"unconditional literal LL stripe > {float(stripe):.10f}")
