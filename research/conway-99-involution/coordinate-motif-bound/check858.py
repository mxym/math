"""Auxiliary integer checks for the analytical coordinate proof."""
from fractions import Fraction

def require(x):
    if not x:
        raise AssertionError("exact arithmetic check failed")

for a3 in range(13):
    a2,a0=36-3*a3,32-a3
    require(a0>=20 and a2>=0 and a2%3==0)
    require(4+a0-a2-2*a3==0)
    require(16+a0+a2+4*a3==84)
    require(64+a0-a2-8*a3==2*a2-12)
require(Fraction(14,3)-Fraction(2,3)==4)
require(33*Fraction(2,3)-66*Fraction(1,3)==0)
require(33*Fraction(4,9)+66*Fraction(1,9)==22)
column_minimum=14*((22+13)//14)
require(column_minimum==28 and 49*56<99*column_minimum<=49*60)
motif_bound=693+Fraction(231*60,84)
require(motif_bound==858 and motif_bound+209286==210144)
print("13 triangle profiles, fractional row floor, and n3 >= 858 verified")
