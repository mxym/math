"""Rational outward verification of the closed-form decimal enclosure in (6)."""
from fractions import Fraction as Q

def require(condition):
    if not condition:
        raise RuntimeError("A rational enclosure check failed")
def atan(x, M):
    s = sum(((-1)**n * x**(2*n+1)/(2*n+1) for n in range(M)), Q(0))
    t = (-1)**M*x**(2*M+1)/(2*M+1)
    return min(s,s+t),max(s,s+t)
a,b=atan(Q(1,5),10); c,d=atan(Q(1,239),5)
pl,pu=16*a-4*d,16*b-4*c
require(Q(31415926,10**7)<pl<pu<Q(31415927,10**7))
x=Q(1,3); M=12
ll=2*sum((x**(2*n+1)/(2*n+1) for n in range(M)),Q(0))
lu=ll+2*x**(2*M+1)/(2*M+1)/(1-x*x)
require(Q(6931471,10**7)<ll<lu<Q(6931472,10**7))
def zeta(k):
    s=sum((Q(1,n**k) for n in range(1,1001)),Q(0))
    return s,s+Q(1,(k-1)*1000**(k-1))
z3l,z3u=zeta(3);z5l,z5u=zeta(5)
lo=pl**4*ll/120-pu**2*z3u/8+15*z5l/16
hi=pu**4*lu/120-pl**2*z3l/8+15*z5u/16
require(Q(51797,10**6)<lo<hi<Q(51800,10**6))
require(4*(Q(1,10)+hi)<Q(608,1000))
print("Six-factor reference enclosure and <0.608 actual upper-bound constant checked.")
