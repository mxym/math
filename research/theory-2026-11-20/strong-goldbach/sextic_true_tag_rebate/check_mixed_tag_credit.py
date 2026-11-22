#!/usr/bin/env python3
"""Outward ordinary amplitudes and genuine two-orientation mixed-chamber bound."""
from fractions import Fraction as F
from math import isqrt, ceil, factorial as fac
from collections import Counter

def require(ok):
 if not ok:raise ArithmeticError("mixed tagged credit certificate failed")
S=10**12;D=1000; LL=100; RR=20
DEN=4*D**6
def raw(i):
 if 2*i>D:return 0
 z=D-2*i
 return z**4*(11*D*D-7*z*z)
P=[raw(t) for t in range(D+1)]
psi=[P[t]-P[D-t] for t in range(D+1)]
def loglo(x):
 q=(x-1)/(x+1)
 return 2*sum(q**(2*j+1)/(2*j+1) for j in range(20))
def loghi(x):
 q=(x-1)/(x+1)
 return loglo(x)+2*q**41/(41*(1-q*q))
def sqrtup(x):
 z=isqrt(x.numerator*S*S//x.denominator)
 return F(z+(z*z*x.denominator!=x.numerator*S*S),S)
def require_geometry():
 def f(t):
  z=F(1,2)-t
  return 44*z**4-112*z**6
 def fp(t):
  z=F(1,2)-t
  return -176*z**3+672*z**5
 def fppp(t):
  return 1152-9024*t+20160*t*t-13440*t**3
 require(fppp(F(".125"))>0 and max(fp(F(".08")),fp(F(".125")))<fp(F(".25")))
 require(1-f(F(".08"))-f(F(".170"))+f(F(".250"))>0)
 require(1-f(F(".080"))-2*f(F(".375"))>0)
 require(loghi(F(100,57))<F(".57"))
require_geometry()
mass=[0]*(LL+1)
def add(hist,top,den,bins,w):
 i=min(bins,(top*bins-1)//den)
 if i>0:hist[i]+=w
for i in range(150,500):
 add(mass,DEN-P[i],DEN,LL,D*S//((i+1)*(D-i)))
for i in range(150,334):
 for j in range(i+1,(D-i-3)//2+1):
  upper=D-i-j
  add(mass,DEN-psi[i]-psi[j]-psi[upper-2],DEN,LL,D*S//((i+1)*(j+1)*upper))
ml=[F(sum(mass[i:]),S) for i in range(1,LL+1)]
t0=170;b=F(t0,D);theta=F(".499");a=F(".150")
k=2/theta*loglo(theta/a-1)
# Common scaled three-quotient simplex; allow full last partial squares.
Q=256
hist=Counter()
for i in range(Q):
 for j in range(Q-i):
  hist[max(u*u+v*v+(Q-u-v)**2 for u in (i,i+1) for v in (j,j+1))]+=1
QP=Q*Q
pos=F(0);neg=F(0)
for i in range(80,125):
 low=F(i,D);high=F(i+1,D);top=1-low
 mr=[0]*(91)
 # Per-unit-tag mass lower: cofactor rank 1
 def addR(top,den,w):
  j=min(90,(top*RR-1)//den)
  if j>0:mr[j]+=w
 addR((DEN-P[i])*D,DEN*(i+1),S*D//(D-i))
 for j in range(t0,(D-i-3)//2+1):
  W=D-i-j
  require(W-2>=j+1)
  addR((DEN-psi[i]-psi[j]-psi[W-2])*D,DEN*(i+1),D*S//((j+1)*W))
 ur=2/(theta-high)
 require(2<(theta-high)/b<3)
 r=[F(sum(mr[z:]),S) for z in range(1,91)]
 val=sum(max(0,k*y-ur*(F("3.8")-x)) for x in ml for y in r)/(LL*RR*D)
 pos+=val
 # rank4 adverse angular upper after exact product cancellation.
 R=top-3*b
 base=1680*(high**2+3*b*b+2*b*R)-528
 slope=1680*R*R/QP
 lcd=base.denominator*slope.denominator
 bb=int(base*lcd);ss=int(slope*lcd)
 B4=R*R*F(sum(v*max(0,bb+ss*z) for z,v in hist.items()),fac(3)*QP*lcd)
 # rank5 C_5 is concave in q and qmean is upper.
 R=top-4*b
 q=high**2+4*b*b+2*b*R+F(2,5)*R*R
 h=sqrtup(q);C=10080*h-1056/h
 B5=C*R**3/(fac(4)*fac(3))
 R=top-5*b
 B6=40320*R**4/(fac(5)*fac(4))
 neg+=2/(3*a)*(B4+B5+B6)/D
require(pos>F(".115328") and neg<F(".058450"))
require(2*(pos-neg)>F(".113"))
print('actual mixed orientation: positive layer lower, negative upper, net lower:',
      float(pos),float(neg),float(pos-neg))
print('two disjoint reflected signs: net > .113:',float(2*(pos-neg)))
