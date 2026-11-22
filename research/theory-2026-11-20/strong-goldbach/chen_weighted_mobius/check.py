#!/usr/bin/env python3
"""Exact sufficient-margin certificate, not a covariance evaluation."""
from fractions import Fraction as F
from math import factorial

def require(ok):
    if not ok:
        raise ValueError("failed exact certificate")

def I(j):
    return F(2**j, factorial(j)*factorial(3*j-1))

theta = F(".499")
a = theta/3
U = a**2/2-a**3+F(3,4)*a**4-a**5/5+F(2,64)/theta
# For j>=3, I(j+1)/I(j)<=1/1980.
r = F(1,1980)
mcomposite = I(2)+I(3)/(1-r)
modd = I(3)+I(5)/(1-r)
s = (F(".204")*F(".796"))**3
require(U<F(".072406"))
require(mcomposite<F(".01670"))
require(F("3.446")*modd<F(".000114"))
require(U*mcomposite<F(".001210"))
margin = 2*(F(".755")*s-F(".000114"))-F(".001210")
require(margin>F(".005"))
print("canonical least receiver, ordinary absolute mass:",float(U),float(mcomposite))
print("true odd-prime upper, true comp-comp upper:",float(F("3.446")*modd),float(U*mcomposite))
print("R coefficient and new sufficient-margin constant:",float(1+2*s),float(margin))
