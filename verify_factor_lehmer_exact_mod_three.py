#!/usr/bin/env python3
"""Exact constants and low-degree arithmetic for the analytic mod-three Mahler minimum."""
from fractions import Fraction as F


def require(test,msg):
    if not test:
        raise AssertionError(msg)


def h(x):
    return 24*x*x+17*x-5


def poly(a,x):
    y=F(0)
    for b in a:y=y*x+b
    return y


C=218; V=F(107,100); B=F(203,125); R=F(431,250); d=12
brackets=[(F(-931893,10**6),F(-931892,10**6)),
          (F(223559,10**6),F(223560,10**6))]
for a,b in brackets:
    require(h(a)*h(b)<0 and not (a<=F(-1,2)<=b),"two simple critical roots")
    N=(2*(1-a))**12*(2*(1+b))**2*max(abs(1+2*a),abs(1+2*b))**10
    require(N<C*C,"outward circle norm")
g=F(3**17,C)/B**24
require(g>1 and g**d>3**12,"coarse lower measure for all D>=12")
r=B**-d
require((1+r)**14*(1+r+r*r)**5<V,"small-disk bound")
z=F(3**17,C)/R**24
require(z>1 and z**d*C*C>3**12*V*V,"degree-uniform strict threshold")
require(F(3**17,C)>R**24,"full-divisibility degree-six comparison")

T=F(461,200)
require(R+1/R<T and (R-1/R)**2<2,"trace radii")
require([a for a in range(-int(T),int(T)+1) if a%3==2]==[-1,2],"degree-two coefficients")
As=[a for a in range(-int(2*T),int(2*T)+1) if a%3==2]
Cs=[c for c in range(-int(T*T),int(T*T)+1) if c%3==0]
require(As==[-4,-1,2] and Cs==[-3,0,3],"quartic coefficient list")
for a in [-4,2]:
    t=T if a<0 else -T
    require(poly((1,a,-3),t)<0,"extra real trace root outside")
require(T<3 and poly((1,-4,3),3)==0,"forbidden trace 3")
for a in [-1,2]:
    require(F(12-a*a,4)>=2,"complex trace exclusion")
require(all(poly((1,-1,-3),x)!=0 for x in [-2,-1,0,1,2]),"no low-degree root of unity")
a,b=F(17220,10000),F(17221,10000)
require(1<a<b<R and poly((1,-1,-1,-1,1),a)*poly((1,-1,-1,-1,1),b)<0,
        "isolated quartic candidate")
print("PASS exact auxiliary norm, analytic all-large-degree gap, and quadratic/quartic checks")
