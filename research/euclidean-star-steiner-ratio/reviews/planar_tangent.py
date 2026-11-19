#!/usr/bin/env python3
# Different computation: build coefficients recursively, Horner both the
# polynomial and its formal derivative. All operations rational.
from fractions import Fraction as F
import math

def check(x):
    if not x:raise ArithmeticError("failed exact comparison")

# Coefficients for -sqrt(1-y) skip the constant.  Angle moments via recurrence.
q=F(1,2); moment=F(1); coeffs=[]; x=F(369,400)
for m in range(1,25):
    if m%2==0:
        moment*=F(m-1,m);coeffs.append(q*moment)
    q*=F(2*m-1,2*m+2)
p=g=F(0)
for c in reversed([F(0)]+coeffs):
    g,p=g*x*x+p,p*x*x+c
# g=P'_y(x^2), where P is a polynomial in y=x².
D=(1-p)/2-(1+x)*2*x*g
V=(1+x)*(1-p)+(1-x)*D
check(0<D<F(1,1600));check(0<V<F(17836,10000))
check(V*V<F(769,400)*F(2573,2000)**2)
check(F(17836,10000)**2<F(769,400)*F(2573,2000)**2)
print("PASS: independent 24-step binomial/moment recurrences, tangent orientation and cleared-radical comparison 2573/2000.")
