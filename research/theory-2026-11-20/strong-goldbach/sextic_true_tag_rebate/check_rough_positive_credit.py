#!/usr/bin/env python3
"""Outward Dickman-2 grid and true ordinary angle-cell lower sums."""
from fractions import Fraction as F
S=10**13
def require(ok):
 if not ok:raise ArithmeticError("rough positive credit certificate failed")
def ceilq(a,b):return (a+b-1)//b
def rho_bounds(u=F("3.32"), K=30000):
 require((u*K).denominator==1)
 n=int(u*K)
 hi=[S]*(K+1);lo=hi.copy()
 for i in range(K,n):
  lo.append(max(0,lo[i]-ceilq(2*(i+1-K)*hi[i-K],i*i)))
  hi.append(max(0,hi[i]-(2*(i-K)*lo[i+1-K])//((i+1)**2)))
  require(lo[-1]<=hi[-1])
 val=sum((2*i+1)*lo[i+1] for i in range(n))
 return F(val,2*K*K*S)
a=F(".15");theta=F(".499");D=F(".499")
I=rho_bounds(D/a)
C=1/(a*a*I)
z=(theta/a-2)/(theta/a)
loglo=2*sum(z**(2*j+1)/(2*j+1) for j in range(20))
k=2/theta*loglo
m0=1000;m1=150;R=200
den=4*m0**6
def raw(t):
 if 2*t>m0:return 0
 z=m0-2*t
 return z**4*(11*m0*m0-7*z*z)
P=[raw(t) for t in range(m0+1)]
psi=[P[t]-P[m0-t] for t in range(m0+1)]
mass=[0]*(R+1)
n2=0;n3=0
def add(scr,weight):
 i=min(R,(scr*R-1)//den)
 if i>0:mass[i]+=weight
for i in range(m1,m0//2):
 add(den-P[i],m0*S//((i+1)*(m0-i)))
 n2+=1
for i in range(m1,m0//3+1):
 for j in range(i+1,(m0-i-3)//2+1):
  upper=m0-i-j
  score=den-psi[i]-psi[j]-psi[upper-2]
  add(score,m0*S//((i+1)*(j+1)*upper))
  n3+=1
means=[F(sum(mass[i:]),S) for i in range(1,R+1)]
credit=sum(max(0,k*(u+v)-C) for u in means for v in means)/R**2
require(C<F("15.613") and k>F("3.384"))
require((n2,n3)==(350,25025) and credit>F(".47"))
print('ordinary rho_2 integral lower, true ambient upper, weighted marginal coefficient:',
      float(I),float(C),float(k))
print('true source angle boxes (rank 2, rank 3):', n2, n3)
print('strict credit > .470:', float(credit))
