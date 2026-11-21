"""Rational certificate for the long-overlap ratios; no floats in bounds."""
from fractions import Fraction as Q


def log_enclosure(r, terms=8):
    if not (r > 1 and terms >= 1):
        raise ValueError((r, terms))
    t = (r-1)/(r+1)
    lo = 2 * sum(t**(2*j+1)/Q(2*j+1) for j in range(terms))
    return lo, lo + 2*t**(2*terms+1)/(Q(2*terms+1)*(1-t*t))


a = Q(31, 200)
u = Q(100, 31)
cb = ((1-log_enclosure(Q(38,31))[0])/(u*(u-1))
      + log_enclosure(Q(51,50))[1]
      + (Q(51,100)-3*a)**3/(36*a**3))
cd = Q(1,100)*(Q(51,100)-2*a)/(2*a*a)
ct = log_enclosure(Q(51,49))[1]
lo = 1-4*cb-2*ct
hi = 3*cb+cd+2*ct
if not (lo > Q(39,100) and hi < Q(52,100)):
    raise ArithmeticError("long-overlap bounds do not pass")
print(f"true negative mass fraction > {float(lo):.10f} (rounded)")
print(f"signed discrepancy fraction < {float(hi):.10f} (rounded)")
