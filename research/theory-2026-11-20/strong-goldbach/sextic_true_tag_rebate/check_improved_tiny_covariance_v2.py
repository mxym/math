"""Rational recheck of the replacement term in the .003 tiny debit."""
from fractions import Fraction as F
from math import prod

def require(claim, label):
    if not claim:
        raise ArithmeticError(label)

b, c, w, k = F(".003"), F(".0135"), F(".070"), 14
z = (w + c) / (w - c)
T0 = 16*z**5 - 20*z**3 + 5*z
lam = (T0 - 1) / (T0 + 1)
C0 = 1 + ((4*w/(w-c))**5 + 1) / (T0+1)
G0 = 1 + C0*C0
R0 = (w-c-b)/b
v0, v1 = 1-c-b, 1-c-b-k*b
rho = G0/prod(R0-j for j in range(k))*(1 + 4**k*v0/v1)
require(R0 == F(107, 6) and R0 > k-1 and k >= 10, "factorial")
require(F(".499")-(c+b+k*b)>3*b and v1>0, "upper receiver")
qt = F(".486499")+c+b+4*b+2*F(".0000001")
m = qt/(1-F(".0000001"))
g = 2*m
require(qt == F(".5149992") and m < F(".515") and g < F("1.03"), "grouped caps")
require(F(".7")*g+F(".25")*m-F(".85") <= -F(".00025"), "BC1")
require(F(".875")*g+F(".125")*m-1 < -F(".034"), "BC2")
require(F(".5")-F(".65")*F(".99")+F(".25")*m < -F(".014"), "BC3")
require(F(".5")-F(".625")*F(".99")+F(".125")*m < -F(".05"), "BC4")
require(lam>F(".96468") and G0<F(2896) and rho<F(".003860"), "polynomial and tail")

BV, BX, BD, UD = F(".009042"), F(".017667"), F(".006657"), F(".007445")
old_square = F(".8")/b*BX**2
new_square = (672*b**5)**2 + (1-lam**2+rho)*old_square
other = (2*F(".228")*F(".01701") + F(".227")**2
         + F("4.298")*(BD+BV) + F("2.594")/10**7
         + (BD+2*BV)*UD + F(".0001"))
budget = other + new_square
require(old_square-new_square>F(".0771365"), "direct gain")
require(budget<F(".133141") and F(".954")-F(".1332")==F(".8208"), "whole debit")
print("lambda =", float(lam), "tail factor =", float(rho))
print("old V-square upper =", float(old_square), "new =", float(new_square))
print("total debit <", float(budget), "< .1332")
