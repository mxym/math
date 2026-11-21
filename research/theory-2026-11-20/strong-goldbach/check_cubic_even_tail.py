#!/usr/bin/env python3
"""Exact rational certificate for the complete cubic even-rank angular upper."""
from fractions import Fraction as F
from math import factorial
from functools import lru_cache

def need(b,msg):
    if not b:
        raise ArithmeticError(msg)

def T_atan(x,n):
    a=sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    b=a+(-1)**n*x**(2*n+1)/F(2*n+1)
    return min(a,b),max(a,b)
a0,a1=T_atan(F(1,5),12)
b0,b1=T_atan(F(1,239),6)
pi0=F(157,50)
need(16*a0-4*b1>pi0,'Machin bound 3.14<pi')
C4,C3=4/pi0,3/pi0

def logone(r,n=13):
    z=(r-1)/(r+1)
    need(0<=z<=F(1,3),'normalized logarithm')
    s=sum((2*z**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    return s, s+2*z**(2*n+1)/((2*n+1)*(1-z*z))
lo2,hi2=logone(F(2))
snap=1<<36

@lru_cache(None)
def logbounds(r):
    e=0
    while r>=2:
        r/=2
        e+=1
    a,b=logone(r)
    a+=e*lo2
    b+=e*hi2
    return F((a*snap).__floor__(),snap),F((b*snap).__ceil__(),snap)

def hupper(u,K=12):
    h=sum((logbounds(1+4*n*n*u*u)[1]/(4*n*n-1) for n in range(1,K+1)),F(0))
    h+=(logbounds(1+4*u*u)[1]+2*(logbounds(F(K))[1]+1))/(K*(4-F(1,(K+1)**2)))
    return C4*h

def even_tail(h,n=40):
    f=sum((h**j/factorial(j) for j in range(8,n+1,2)),F(0))
    z=h*h/((n+3)*(n+4))
    need(z<1,'cosh remainder')
    return f+h**(n+2)/factorial(n+2)/(1-z)

def expup(h,n=40):
    f=sum((h**j/factorial(j) for j in range(n+1)),F(0))
    need(h<n+2,'exp remainder')
    return f+h**(n+1)/factorial(n+1)/(1-h/(n+2))

total=F(0)
M=32
for e in range(-2,7):
    val=F(2)**e
    for i in range(M):
        a=val*(1+F(i,M))
        b=val*(1+F(i+1,M))
        value=even_tail(hupper(b))*(a**-3-b**-3)/3
        total+=F((value*snap).__ceil__(),snap)
small=F(2**8,factorial(8))*F(1,4)**5/F(5)*2
U=F(128)
large=expup(hupper(U))/(2*(3-C4)*U**3)
angular=C3*(small+total+large)
need(angular < F(155,10000), 'angular absolute <.0155')
Jhi=logbounds(F(7,5))[1]-F(1408,10000)
need(F(24,5)*Jhi*angular/2 < F(73,10000),'even adverse <.0073 M')
need(F(172,100)/F(359,1000)<F(24,5),'real q sieve factor')
print(f'Certified abs angular < {float(angular):.9f}, actual upper limsup < {float(F(24,5)*Jhi*angular/2):.9f} M')
