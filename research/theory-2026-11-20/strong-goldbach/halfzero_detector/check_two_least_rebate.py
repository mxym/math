#!/usr/bin/env python3
"""Exact lower replay for the genuine two-least-tag prime rebate."""
from fractions import Fraction as Q
from math import ceil

def require(condition):
    if not condition:
        raise ValueError("exact inequality failed")
SCALE=10**12
NGRID=1000
NG=7000
J=[[SCALE]*(NG+1)]
for j in range(2,9):
 z=[0]*(NG+1)
 for i in range(NGRID+1,NG+1):
  z[i]=z[i-1]+(J[-1][i-NGRID]+i-2)//(i-1)
 J.append(z)
D0=Q(555,1000); coeff=Q(3446,1000)
def safe_log(x):
 t=(x-1)/(x+1)
 return 2*sum(t**(2*j+1)/(2*j+1) for j in range(7))
def choose(A,B):
 u=Q(A+1,1000);v=Q(B+1,1000)
 lo=1-u-v; hi=lo+Q(2,1000)
 D=D0-u-v
 z=max(Q(1325,10000),D/3)
 s=D/z
 require(2<s<=3 and hi/z<8 and z>v and z<Q(187,1000))
 k=ceil((hi/z-1)*1000)
 C=coeff*sum(Q(j[k],SCALE) for j in J[3:])/lo
 L=2*safe_log(s-1)/D
 W=min(36*lo**2-14,144*z*(lo-z),Q(7,5)*288*z*z*(lo-2*z))
 require(W>0)
 require(2*Q(132,1000)**2+2*z*z+(hi-2*z)**2 < Q(25,49))
 return max(Q(0),L-C)*W
# lower floor round safe to 10^-9, avoid summing giant distinct denominators.
ans_scaled=0
mn=100
for i in range(5,132):
 for j in range(i+1,132):
  x=choose(i,j)
  ans_scaled+=int(x*10**9)
  mn=min(mn,x)
require(ans_scaled == 105769197972637)
require(Q(ans_scaled,10**15) > Q(105,1000))
print(f"exact lower = {ans_scaled}/10^15 = {float(Q(ans_scaled,10**15)):.15f}")
