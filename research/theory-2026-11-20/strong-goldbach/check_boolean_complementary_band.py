#!/usr/bin/env python3
"""Exact algebra and rational enclosure; neither samples actual prime occupancy."""
from fractions import Fraction as F
from itertools import combinations, product

def require(cond, msg):
    if not cond:
        raise ArithmeticError(msg)

def log_band(y, n=36):
    z = (y-1)/(y+1)
    require(0 < z < 1, 'log input')
    p = sum((2*z**(2*k+1)/F(2*k+1) for k in range(n)), F(0))
    return p, p + 2*z**(2*n+1)/((2*n+1)*(1-z*z))

t0,t1=F(105,1000),F(135,1000)
a,b=log_band(t1/t0)
d,e=log_band(F(95,51))
jl=a-4*(t1-t0)+2*(t1*t1-t0*t0)
ju=b-4*(t1-t0)+2*(t1*t1-t0*t0)
coeff_l=jl*d*d/2*8*F(28,100)
coeff_u=ju*e*e/2*8*F(28,100)
require(F(63149,10**6)<coeff_l<coeff_u<F(63150,10**6),'strict .063149 enclosure')
for count in range(9):
    for size in range(count+1):
        chosen=range(size)
        mob=sum((-1)**(j+1)*len(list(combinations(chosen,j))) for j in range(1,size+1))
        require(mob==int(size>0),'Boolean identity')
        for other,u,C in product(range(5),(0,1),range(-15,2)):
            old,new=size+other,mob+other
            require(0 <= new <= old,'V ordering')
            if C<0 or u==0 or old!=0:
                require(max(0,C*(u-new))<=max(0,C*(u-old)), 'positive-part sign')
require(F(95,100)*F(30,100)==F(285,1000),'tag exponent')
require(1-F(14,100)-F(285,1000)-F(1,2)==F(75,1000),'free interval')
print('Boolean sign and .063149 < coefficient < .063150 checked')
