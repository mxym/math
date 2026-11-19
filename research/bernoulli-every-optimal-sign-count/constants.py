"""Exact rational audit of cutoffs in the effective Fourier comparison (n>=150)."""
from fractions import Fraction as F
from math import factorial

def check(label, condition):
    if not condition:
        raise ArithmeticError(label)
    print("PASS", label)

n=150
check("8 lambda/pi^2 >=2/3, using pi^2<10",F(8*8,9*10)>=F(2,3))
check("Gaussian tenth moment error",945<31**2 and 31*F(9,40)<7)
check("outer bound and monotonicity",2*n**4*F(3,4)**n<F(1,1000)
      and F(n+1,n)**4*F(3,4)<1)
check("upper loss", (F(5,12)+F(7,n))**2+F(1,1000)<F(1,4))
check("w window and signed phase",n*F(8,9)>11**2 and (2+F(9,8))*F(3,11)<1)
check("cubic shape bound",F(1,3)+F(2,5)*F(3,11)**2<F(3,8))
check("window weight",1-F(81,4*(n-9))>F(5,6))
check("Gaussian tail coefficient",sum(F(9,2)**i/factorial(i) for i in range(9))>F(250,3)
      and F(2,3)<F(5,6)**2 and (42+F(2,3))/100<F(7,16))
check("norm floor",F(3,4)-F(7,n)*F(5,2)==F(19,30))
check("odd j competitor gap",F(3*n-2,n+1)>F(5,2) and 1-F(1,n*n)-F(1,2*n)>F(99,100)
      and F(99,100)**2>F(9,10))
check("strict lower-vs-upper separation",F(5,6)*F(11,12)*F(19,30)**2*F(9,10)==F(3971,14400)>F(1,4))
