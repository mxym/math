#!/usr/bin/env python3
from fractions import Fraction as F

def require(v,msg):
 if not v:raise ArithmeticError(msg)

pi_lo=16*(F(1,5)-F(1,5)**3/3+F(1,5)**5/5-F(1,5)**7/7)-F(4,239)
require(pi_lo>F(157,50),'Machin pi lower bound')
bound=(F(2,3)+F(1,160))/F(157,50)
require(bound==F(1615,7536),'large-d rational simplification')
x=F(451,500);sm=F(1);term=F(1)
for j in range(1,11):term*=x/j;sm+=term
require(bound<F(87,1000)*sm,'large-d strict Taylor comparison')

# Exact exponential upper: after term N, every later ratio is <=x/(N+2).
x=F(1049,1000);N=12;sm=F(1);term=F(1)
for j in range(1,N+1):term*=x/j;sm+=term
first_omitted=term*x/(N+1)
exp_upper=sm+first_omitted/(1-x/(N+2))
require(exp_upper<F(571,200),'final upper endpoint e^1.049 <2.855')

# Exact square identity regression at representative rational points.
for r,s,x,y in [(160,160,F(1),F(2)),(160,200,F(2,3),F(5,7)),(1,5,F(7,3),F(4)),(5,5,F(6),F(6))]:
 n=r+s;de=4*r*s+3*n+2;k=F(3*n+2,de);B=(s*x+r*y)/n
 G=x*x/(r+1)+y*y/(s+1)-(r*x+s*y)**2/(n*n*(n+1))
 rhs=F(r*s,(r+1)*n*n*(s+1)*(n+1)*de)*((s+1)*(3*r+s+2)*x-(r+1)*(r+3*s+2)*y)**2
 require(G-k*B*B==rhs,'quadratic exact identity regression')
print('PASS: exact mixed-potential large-d closure constants for r,s >=160.')
print('PASS: Machin pi bound, nonnegative-square identity regressions, and e^1.049 <2.855.')
