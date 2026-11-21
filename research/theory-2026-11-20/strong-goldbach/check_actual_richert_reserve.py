"""Exact bracket and final normalization for the actual Richert reserve."""
from fractions import Fraction as F

def log_bounds(q, terms=30):
    if q <= 1:
        raise ArithmeticError(q)
    r=(q-1)/(q+1)
    lo=2*sum((r**(2*k+1)/F(2*k+1) for k in range(terms)), F(0))
    return lo, lo+2*r**(2*terms+1)/((2*terms+1)*(1-r*r))

D=F(405,1000)
z=F(102,1000)
y=F(360,1000)
eta=F(133,100)
if not (2<D/z<4 and (D-z)/z<3 and (D-y)>0
        and F(90,1000)+D<F(1,2) and F(90,1000)<z
        and 4-F(960,1000)/y>eta):
    raise ArithmeticError("sieve and rank margins")
B=2/D*log_bounds(D/z-1)[0] - 2/(eta*D)*log_bounds(y/z)[1]
B+=2/eta*(1/y-1/D)*log_bounds((D-z)/(D-y))[0]
p=log_bounds(F(9,4))[0]
if not (B>F(157,100) and p>F(81,100)
        and F(17,18)*F(157,100)*F(81,100)>F(119,100)):
    raise ArithmeticError((B,p))
print("Certified lower bracket and harmonic mark:", float(B),float(p))
print("Certified stronger normalized reserve:", float(F(17,18)*B*p))
