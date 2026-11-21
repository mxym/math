from fractions import Fraction as F
from math import comb, factorial

coeffs=(F(2497,3430),-F(782,1715),F(1119,6860),-F(33,980),F(11,3430))
def phi(k):
    return sum((c*comb(k,h) for h,c in enumerate(coeffs,1)), F(0))
if not all(0<=phi(k)<=1 for k in range(26)):
    raise ArithmeticError("infeasible bounded partition")
r=F(5,13)
lo=2*sum((r**(2*k+1)/F(2*k+1) for k in range(30)), F(0))
hi=lo+2*r**61/(61*(1-r*r))
theta_lo=sum(c*(lo if c>0 else hi)**h/factorial(h)
               for h,c in enumerate(coeffs,1))
theta_hi=sum(c*(hi if c>0 else lo)**h/factorial(h)
               for h,c in enumerate(coeffs,1))
reserve=phi(1)*F(157,100)*F(81,100)
if not (F(454,1000)<theta_lo<=theta_hi<F(455,1000)
        and reserve>F(9257,10000) and reserve-theta_hi>F(47,100)):
    raise ArithmeticError((theta_lo,theta_hi,reserve))
print("Certified net coefficient",float(theta_lo),float(theta_hi))
print("Certified marked negative and compensation",float(reserve),float(reserve-theta_hi))
