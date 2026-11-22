"""Rational recheck of the old high four-tag ledger with the sharp sign bound."""
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt
from pathlib import Path

def need(p, tag):
    if not p:
        raise ArithmeticError(tag)

p = Path(__file__).resolve().with_name("check.py")
need(sha256(p.read_bytes()).hexdigest() ==
     "02f0825382ebc43eb9eebb041c920cf88963b283294750f9358f4943f223bd2b",
     "different certified angular bounds")

def sqrt_up(q, scale=10**12):
    a,b=q.numerator*scale*scale,q.denominator
    z=isqrt(a//b)
    return F(z+(z*z*b<a),scale)

M=[F(t)/2 for t in (".01933",".00345",".000534",".000078",".0000114")]
U=[F(t)/2 for t in (".373","1.232","12.850","8.679","35.095")]
mixed=sum(min(u*F(".009042"),
              sqrt_up(u*x*F(".017667")**2*F(".8")/F(".003")))
          for u,x in zip(U,M))
self_cost=sum(min(u*y,v*x) for u,x in zip(U,M) for v,y in zip(U,M))
old_overlap=2*F(".1212")*sum(M)
total=2*((F("2.446")+F(".228")+F(".007445"))*sum(M)+mixed)
total+=self_cost+old_overlap
need(total<F(".123897"),"true full replacement debit")
print("exact outward debit",float(total),"< .123897 < .124")
