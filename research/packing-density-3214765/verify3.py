#!/usr/bin/env python3
"""Exact Sylvester determinant/interpolation and monotone root isolation for [3,1,3]."""
from fractions import Fraction as Q
from itertools import zip_longest
from math import prod

def ok(b,msg):
    if not b: raise ValueError(msg)
# All coefficient vectors use ascending degree in z.
def add(a,b):return [x+y for x,y in zip_longest(a,b,fillvalue=0)]
def scale(a,k):return [x*k for x in a]
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def cube(a):return mul(mul(a,a),a)
def horner(f,x):
    out=0
    for c in reversed(f):out=out*x+c
    return out
T=(-432,2565671328,20668776552,4575974416,-439508172703,-1682183144550,
   -2635934939569,-1771652618180,-506074249089,-40641373350,3363968313)
def pair(r):
    A=scale([1+3*r*r,2*r*(3+r*r),1+3*r*r],r)
    M=mul([r,1],[1,r])
    B=scale(M,1-r*r)
    V=mul([1,0,-1],M)
    U=r*(1-r*r)**2
    p=[r*(3+r*r),0,-3*r*(3+r*r),-2*(1+3*r*r)]
    E=add(scale(cube(add(scale(B,6),scale(A,3))),U),
          scale(mul(V,cube(add(B,scale(A,4)))),-1))
    return p,E
def resultant(p,e):
    def rows(poly,count):
        return [[0]*j+poly[::-1]+[0]*(count-1-j) for j in range(count)]
    a=rows(p,len(e)-1)+rows(e,len(p)-1)
    n=len(a); prev=sgn=1
    for k in range(n-1):
        if not a[k][k]:
            i=next((i for i in range(k+1,n) if a[i][k]),None)
            if i is None:return 0
            a[i],a[k]=a[k],a[i];sgn=-sgn
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                den=pivot*a[i][j]-a[i][k]*a[k][j]
                q,rem=divmod(den,prev);ok(not rem,'non-exact Bareiss division')
                a[i][j]=q
        prev=pivot
    return sgn*a[-1][-1]
def main():
    # deg_z(P)=3, deg_z(E)<=10, deg_r(P)<=3, deg_r(E)<=17;
    # both sides of the desired identity have r-degree <=81.
    for r in range(2,84):
        p,e=pair(r)
        ok(len(p)==4 and len(e)==11 and p[-1]*e[-1]!=0,'degrees')
        ok(resultant(p,e)==12*r**4*(r*r-1)**22*horner(T,r*r),'resultant')
    B=Q(1,49)
    m=T[1]+sum(min(0,i*T[i])*B**(i-1) for i in range(2,len(T)))
    ok(m>2_500_000_000 and horner(T,0)<0<horner(T,B),'monotonicity and signs')
    a,b=Q(41033736796,10**14),Q(41033736799,10**14)
    ok(horner(T,a*a)<0<horner(T,b*b),'r bracket')
    c,d=Q(8445258235,10**11),Q(8445258236,10**11)
    # R(r)=r(3+r²)/(1+3r²) strictly increasing: derivative 3(1-r²)^2/(1+3r²)^2.
    f=lambda r,z:r*(3+r*r)*(1-3*z*z)-2*z**3*(1+3*r*r)
    ok(f(a,c)>0>f(b,d),'z bracket')
    print('82 exact 13x13 Sylvester determinants certify the polynomial identity.')
    print('T is increasing on [0,1/49], with derivative > 2500000000.')
    print('r in',a,b,'; z in',c,d)
if __name__=='__main__':main()
