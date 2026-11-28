#!/usr/bin/env python3
"""Exact rational controls for the three-coincidence spacing note."""
from itertools import combinations
from collections import defaultdict
from math import comb, prod, lcm
from fractions import Fraction as F


def require(test, msg):
    if not test:
        raise AssertionError(msg)


def sign(z,y,a,b):
    D=lcm(z.denominator,y.denominator)
    Z=int(z*D); Y=int(y*D)
    A=prod(Z-j*D for j in range(a+b))
    B=prod(Z+Y-j*D for j in range(a))*prod(Y+j*D for j in range(1,b+1))
    return (A>B)-(A<B)


def bracket(z,a,b):
    lo,hi=F(0),z
    require(sign(z,lo,a,b)>0 and sign(z,hi,a,b)<0,"initial branch bracket")
    for _ in range(50):
        mid=(lo+hi)/2
        if sign(z,mid,a,b)>0:
            lo=mid
        else:
            hi=mid
    return lo,hi


for s in [16,32,64,128,256,500]:
    M=2*s+1
    t1,t2=F(s-1,s),F(M-2,M)
    require(t2-t1==F(1,s*M),"Farey determinant")
    zlo,zhi=F(8,25)*M**3,F(2,5)*M**3
    for z,is_low in [(zlo,True),(zhi,False)]:
        l,u=bracket(z,1,s-1)
        L,U=bracket(z,2,M-2)
        require(U<l if is_low else L>u,"opposite exact branch signs")
    # A rational upper bound on alpha_1 and the elementary upper squeeze
    # certify the lower-half restriction throughout this real bracket.
    x=1-F(1,2*s)
    require((1+x)*x**(s-1)>1 and (1-x)*zlo>M+(M-2),
            "whole bracket lies on the lower half at any crossing")

seen=defaultdict(list)
for n in range(2,201):
    for k in range(1,n//2+1):
        seen[comb(n,k)].append((n,k))
checked=0
for bucket in seen.values():
    for p2,p1,p0 in combinations(bucket,3):
        n,k=p0
        a1,b1=n-p1[0],p1[1]-k
        a2,b2=n-p2[0],p2[1]-k
        s1,s2=a1+b1,a2+b2
        require(a1>0 and b1>0 and a2>a1 and b2>b1,"monotone half-row order")
        require(0<s1<s2 and b2*s1>b1*s2,"strict slope order")
        require(n<9*s2**3,"finite cubic bound")
        checked+=1
require(checked>=1,"integer controls include repeated triples")
print(f"PASS: six exact continuous sign brackets and {checked} integer coincidence triples")
