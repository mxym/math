#!/usr/bin/env python3
"""Exact ordinary rank-four mass and the literal overlaps with both compensated banks."""
from fractions import Fraction as F
from math import ceil, isqrt

def require(b):
    if not b:
        raise ValueError("rational certificate failed")

scale=10**12
grid=1000
J=[[scale]*7001]  # J_1
for j in range(2,9):
    row=[0]*7001
    for i in range(1001,7001):
        row[i]=row[i-1]+(J[-1][i-1000]+i-2)//(i-1)
    J.append(row)
def lowlog(x):
    t=(x-1)/(x+1)
    return 2*sum(t**(2*j+1)/(2*j+1) for j in range(7))
def rup(x):
    return F(ceil(10**15*x),10**15)

def mass(i,j,second):
    p,q=F(i+1,1000),F(j+1,1000)
    c=1-p-q
    C=c+F(2,1000)
    D=F(555,1000)-p-q
    z=max(F(1325,10000),D/3,q+F(5,10000) if second else F(0))
    if not (2<D/z<=3 and C/z<8 and q<z<F(187,1000)):
        require(second)
        return F(0)
    idx=ceil((C/z-1)*grid)
    upper=F(3446,1000)*sum(F(row[idx],scale) for row in J[3:])/c
    if 2*lowlog(D/z-1)/D<=upper:
        require(second)
        return F(0)
    if second:
        U=p*p+q*q+2*z*z+(C-2*z)**2
        height=F(isqrt((10**6*U.denominator)//U.numerator),1000)
        require(height**2*U<=1)
        weight=min(36*c*c+12*(F(i,1000)**2+F(j,1000)**2)-14,
                   144*z*(c-z),288*height*z*z*(c-2*z))
    else:
        require(2*F(132,1000)**2+2*z*z+(C-2*z)**2<F(25,49))
        weight=min(36*c*c-14,144*z*(c-z),288*F(7,5)*z*z*(c-2*z))
    require(weight>0)
    return rup(weight*sum(F(row[idx],scale) for row in J[:3])/(c*10**6))

m1=sum(mass(i,j,False) for i in range(19,58) for j in range(i+1,132))
m2=sum(mass(i,j,True) for i in range(19,58) for j in range(132,187))
require(m1==F(68376989696821,10**15))
require(m2==F(32632444367893,10**15))
require(m1<F(68376990,10**9) and m2<F(32632445,10**9))
raw0=(1-4*F(12,1000))**3-(1-4*F(76,1000))**3
raw1=(1-4*F(19,1000))**3-(1-4*F(58,1000))**3
net0=raw0-F(146748616+77025550,10**9)
net1=raw1-F(68376990+32632445,10**9)
require(raw0==F(525647872,10**9) and raw1==F(335904192,10**9))
require(net0==F(301873706,10**9) and net1==F(234894757,10**9))
require(21*net0>6 and 21*net1>F(48,10))
require(6*F(4,1000)+F(48,10)*F(14,1000)>F(91,1000))
print("ordinary I0 and I1 lower masses:",net0,net1)
print("I1 literal first-bank and second-bank overlap uppers:",m1,m2)
