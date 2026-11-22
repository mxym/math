"""Directed, exact rational check of the two-window Bonferroni constant."""
from fractions import Fraction as F

SCALE = 10**12
CELLS = 1024


def floor_scaled(q):
    return q.numerator * SCALE // q.denominator


def ceil_scaled(q):
    return -floor_scaled(-q)


def log_bounds(q):
    if q <= 1:
        return F(0), F(0)
    t = (q - 1) / (q + 1)
    lo = 2 * sum((t**(2*j+1) / (2*j+1) for j in range(8)), F(0))
    hi = lo + 2*t**17 / (17*(1-t*t))
    return F(floor_scaled(lo), SCALE), F(ceil_scaled(hi), SCALE)


def integrate_bounds(left, right, bounds):
    step = (right-left)/CELLS
    l = h = 0
    for j in range(CELLS):
        a = left + j*step
        b = a + step
        lo, hi = bounds(a, b)
        l += floor_scaled(step * lo)
        h += ceil_scaled(step * hi)
    return F(l, SCALE), F(h, SCALE)


u0, u1 = F('.003'), F('.048')
c0, c1, s = F('.1005'), F('.0995'), F('.6')
v0, v1 = c0-u1, c1-s*u0


def B(u):
    return log_bounds((c1-s*u)/(c0-u))


def first_bounds(a, b):
    # The reciprocal length B(u) is increasing, since c1-s*c0>0.
    return B(a)[0]/b, B(b)[1]/a


def second_bounds(a, b):
    return F(0), B(b)[1]**2/a


def third_bounds(a, b):
    # Upper bound on the ratio for every vertical section in this cell:
    # numerator is nonincreasing, as is the positive denominator.
    nu = min(u1, (c1-a)/s)
    de = max(u0, c0-b)
    return F(0), log_bounds(nu/de)[1]**2/a


mu_l, mu_u = integrate_bounds(u0, u1, first_bounds)
_, s_u = integrate_bounds(u0, u1, second_bounds)
_, t_u = integrate_bounds(v0, v1, third_bounds)
budget = mu_l-(mu_u**2+s_u+t_u)/2
if not (mu_l > F('.197') and mu_u < F('.200') and
        s_u < F('.030') and t_u < F('.080') and budget > F('.12')):
    raise SystemExit(f"exact enclosures insufficient: {mu_l} {mu_u} {s_u} {t_u} {budget}")
print(f"mu in [{mu_l}, {mu_u}], B2 <= {s_u}, A2 <= {t_u}, lower mass = {budget}")
