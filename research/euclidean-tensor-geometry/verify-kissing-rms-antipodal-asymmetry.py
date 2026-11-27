#!/usr/bin/env python3
"""Exact weighted fourth-harmonic and RMS midpoint-gap checks; no dependencies."""
from fractions import Fraction as F
from math import comb,isqrt
if not __debug__:raise RuntimeError('enable assertions')
def add(*a):
    q=[F(0)]*max(map(len,a))
    for z in a:
        for j,x in enumerate(z):q[j]+=x
    return q
def mul(*a):
    r=[F(1)]
    for z in a:
        b=[F(0)]*(len(r)+len(z)-1)
        for i,x in enumerate(r):
            for j,y in enumerate(z):b[i+j]+=x*y
        r=b
    return r
def c(a,z):return mul([F(a)],z)
def bern(poly,H):
    n=len(poly)-1
    return [sum(poly[i]*H**i*F(comb(k,i),comb(n,i))for i in range(k+1))for k in range(n+1)]
rows=[(6,73,360,64),(6,74,512,0),(6,75,540,43),(6,76,681,0),
      (7,127,215,66),(7,128,306,0),(7,129,339,47),(7,130,420,0),
      (7,131,429,31),(7,132,500,0)]
for d,N,H0,b0 in rows:
    P={6:36,7:63}[d];p=N//2;K=isqrt(p-1)+1;H=F(H0,10000);b=F(b0,100)
    assert K*K>=p and bool(b)==bool(N%2)
    if b:
        assert F(1,16)>=F(9,4)*(K+F(1,2))*H**2+F(5,4)*(K+1)**2*H**3
    E=[0,0,p];EE=mul(E,E)
    lo=add(c(p,mul([1,0,-1],[1,0,-1])),[b])
    lo=c(F(3,4*P),mul(lo,lo))
    diag=c(F(3,4),add([p+b*b],c(-4,E),c(6,EE)))
    pair=add(c(F(3,16),add(c(p,E),EE)),
             mul(add([1],c(F(1,2),E)),add([1+F(K,2)],c(F(3,8),E)),EE))
    mixed=c(2*b,[0,F(p,8),F(21*p,16),F(9*p,4),F(5*p,4)])
    difference=add(lo,c(-1,diag),c(-1,pair),c(-1,mixed),[-b*b/12])
    bs=bern(difference,H)
    assert min(bs)>0,(d,N,bs)
    print(d,N,'RMS >',H,'Bernstein gap >',int(min(bs)*10**7),'e-7')
