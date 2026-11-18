#!/usr/bin/env python3
"""Exact symbolic and finite checks for PROOF.md; no external resources."""
import sympy as s
import itertools
from fractions import Fraction
r,t,d,b,x,u=s.symbols("r t d b x u")
mu=d-r*t
h=(r+1)*(t-1)+1
n=(d-r)*(d+t)/mu
f=d*(d+t)*(t-1)/(mu*(r+t))
g=d*(d-r)*(r+1)/(mu*(r+t))
def ident(expr):
    if s.cancel(expr)!=0: raise AssertionError(s.factor(expr))
def require(val):
    if not val: raise AssertionError(val)
D=1+d/t
L=1+d/h
F=lambda x:n*d*(1-1/x)-d*d-(x-1)*r*r
ident(1+f+g-n);ident(d+f*r-g*t);ident(d*d+f*r*r+g*t*t-n*d)
ident(n-(d+h+r*t*(h-1)/mu))
ident(D-n*(r+1)/(n-d+r))
B=d*h*b-(d+h)*r*r
ident((F(L)-d*B/(h*(h+d))).subs(b,r*t*(h-1)/mu))
B=B.subs(d,r*t*(1+(h-1)/b))
ident(s.diff(B,b) - (r*t*h +r**3*t*(h-1)/b**2))
ident(B.subs(b,1)-r*h*(t*(h-r*r)-r))
ident(h-r*r-(r+1)*(t-r))
ident((t*(h*(u+2)-r*r)-r*h).subs(r,t+u)-(u*u*(t*t-3*t+1)+u*(t**3-2*t*t-t)))
ident(B.subs({t:2,b:r})-r*(-r*r+6*r+4))
ident(F(D)-d*r/(mu*t)*(d*t*(t-1)-r*mu))
ident(F(f+1)*(f+1)-((f+1)*g*t*t-n*d))
ident(n*d/(g*t*t)-(r+t)*(d+t)/((r+1)*t*t))
S=r-t*t+2*t; K=r*((2*t-1)*r+t*t)/S
ident((d+r)*(t-1)**2-(r+1)*(d+r-2*r*t)-S*(K-d))
J=d*(t-1)*(r+1)*t*t-mu*(r+t)**2
ident((f-(r+t)*(d+t)/((r+1)*t*t))*mu*(r+t)*(r+1)*t*t/(d+t)-J)
ident(S*J.subs(d,K)-r*r*(t-1)*(r*(2*t**3-2*t*t-2*t-r)+t**4-2*t*t))
H=2*(d-r)*(r+t)*(r+1)*t*t-2*d*(t-1)*(r+1)*t*t-d*(t-1)*(r+t)*(d+t)
ident(2*n/f-2-(2*(d-r)*(r+t)/(d*(t-1))-2))
ident((2*n/f-2-(r+t)*(d+t)/((r+1)*t*t))*d*(t-1)*(r+1)*t*t-H)
ident(H.subs(d,r*t)-r*t*t*(r+1)*(r-t)*(t-1))
coeffs=[t**5*(t+1)*(3*t**6+3*t**5-2*t**4+10*t**3-3*t**2+3*t+2),2*t**3*(2*t**7+4*t**6+11*t**5+t**4+9*t**3+6*t**2+3),t**2*(12*t**5+6*t**4+26*t**3+t**2+10*t+5),2*t*t*(6*t*t+5),4*t-1]
ident((S*S*H.subs(d,K)/(r*(t-1))).subs(r,t**3+u)-sum(a*u**i for i,a in enumerate(coeffs)))
require(all(min(s.Poly(a.subs(t,2+x),x).all_coeffs())>0 for a in coeffs))
rr=[(r_,m,Fraction((m+2*r_)*(m+2*r_+2),m*(r_+2))) for r_,m in itertools.product(range(3,8),range(1,9)) if m*(r_-2)>4*r_ and (2*r_*(r_+1))%m==0]
require(rr==[(6,7,Fraction(57,8)),(7,7,Fraction(23,3)),(7,8,Fraction(22,3))])
print('PASS: all displayed endpoint, auxiliary, Krein and order/multiplicity identities; shifted polynomial certificate; exact finite residues.')
