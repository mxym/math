#!/usr/bin/env python3
"""Rational replay of both disjoint rebates and the new receiver bound."""
from fractions import Fraction as Q
from math import ceil, isqrt

def require(b):
    if not b:
        raise ValueError("certificate inequality failed")

scale = 10**12
grid = 1000
J = [[scale] * 7001]  # J_1
for j in range(2, 9):
    row = [0] * 7001
    for k in range(1001, 7001):
        row[k] = row[k-1] + (J[-1][k-1000] + k-2)//(k-1)
    J.append(row)
def lowlog(x):
    t = (x-1)/(x+1)
    return 2*sum(t**(2*j+1)/(2*j+1) for j in range(7))
def bhigh(t):
    return Q(3446,1000)*sum(Q(row[ceil((t-1)*grid)],scale)
                             for row in J[3:])

def reb(i,j,old=False):
    a,b=Q(i+1,1000),Q(j+1,1000)
    h=a+b
    c=1-h
    C=c+Q(2,1000)
    D=Q(555,1000)-h
    z=max(Q(1325,10000),D/3,b+Q(5,10000)) if not old else max(Q(1325,10000),D/3)
    if not (2 < D/z <= 3 and C/z < 8 and b < z < Q(187,1000)):
        require(not old)
        return None
    l = max(Q(0),2*lowlog(D/z-1)/D-bhigh(C/z)/c)
    if old:
        W=min(36*c*c-14,144*z*(c-z),Q(7,5)*288*z*z*(c-2*z))
        require(a*a+b*b+2*z*z+(C-2*z)**2 < Q(25,49))
    else:
        U=a*a+b*b+2*z*z+(C-2*z)**2
        B=Q(isqrt((10**6 * U.denominator)//U.numerator),1000)
        require(B**2 * U <= 1)
        W=min(36*c*c+12*(Q(i,1000)**2+Q(j,1000)**2)-14,
              144*z*(c-z), B*288*z*z*(c-2*z))
    require(W>0)
    return Q(int(l*W*10**9),10**15),l*W,a,b,z,c,C,W

def grow(A,B,multiple):
    return Q(ceil(A*multiple),multiple) + B

def tag_totals():
    own=early=joint_lp=0
    d_m=d_U=d_A=0
    theta=Q(499,1000)
    for i in range(5,132):
        for j in range(i+1,187):
            old=j<132
            row=reb(i,j,old)
            if row is None:
                continue
            p,B,a,b,z,c,C,W0=row
            rr=6*c*c+Q(i+j,1000)**2
            require(rr>Q(7,3))
            ratio=(rr-Q(31,20))/(Q(3,4)*rr-Q(7,4))
            require(Q(4,3)<ratio<Q(21,5))
            joint_lp+=Q(int((Q(21,5)-ratio)*p*10**15),10**15)
            if old:
                early+=p
                continue
            own+=p
            if B>0:
                ix=ceil((C/z-1)*1000)
                Dp=theta-a-b
                require(1<Dp/z<3)
                d_m=grow(W0*sum(Q(item[ix],scale) for item in J[:3])/c/10**6,
                         d_m,10**15)
                d_U=grow(2*W0/Dp/10**6,d_U,10**15)
                d_A+=1
    require(early==Q(105769197972637,10**15))
    require(own==Q(28817505038252,10**15))
    require(early+own>Q(134,1000))
    require(joint_lp==Q(315706369439743,10**15))
    result=(Q(263,1000)+joint_lp)/Q(21,5)
    require(result>Q(137,1000))
    require(d_A==3661 and d_m<Q(77025550,10**9) and d_U<Q(141638208,10**9))
    print("prior selected cells:",early)
    print("new disjoint selected cells:",own)
    print("combined disjoint crossings:",early+own)
    print("additional weighted lower:",joint_lp)
    print("combined unpartitioned true crossing >",float(result))
    print("new deweighted bank:",d_A,"cells; ordinary upper",d_m,
          "and receiver upper",d_U)
tag_totals()
