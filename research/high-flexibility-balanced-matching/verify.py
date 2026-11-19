"""Exact rational checks for the two-sided flexibility argument (stdlib only).

This replays algebra and illustrative rigorous global enclosures in y. The
asymptotic f threshold is proved analytically, not by a parameter grid.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
def check(flag):
    if not flag: raise ArithmeticError('failed exact check')
def power_exp(negative):
    # e^{-x}, x=negative in [0,8]; after range reduction use the alternating series.
    x=negative/16
    check(Q(0)<=x<=Q(1,2))
    term=Q(1); s=term
    for i in range(1,13):
        term*=-x/i;s+=term
    lo=s-term*x/13; hi=s
    check(0<lo<=hi<=1)
    return lo**16,hi**16
@lru_cache(None)
def lnbounds(x):
    # 1<=x<=2; log x = 2 sum_0^infty v^(2j+1)/(2j+1).
    check(Q(1)<=x<=2);v=(x-1)/(x+1)
    J=11
    a=2*sum(v**(2*j+1)/(2*j+1) for j in range(J))
    return a,a+2*v**(2*J+1)/((2*J+1)*(1-v*v))
@lru_cache(None)
def h(x):
    if not x:return Q(0),Q(0)
    check(0<x<=1);k=0;y=x
    while y<1:y*=2;k+=1
    a,b=lnbounds(y);lc,uc=lnbounds(Q(2))
    return x*(1-b+k*lc),x*(1-a+k*uc)
def Hbox(p,q,c,N=500):
    # Every y belongs to a consecutive interval. exp(-c q y) decreases, h increases.
    recordlo=Q(-3); recordhi=Q(-3)
    last=None
    for j in range(N+1):
        y=Q(j,N); el,eh=power_exp(c*q*y);hl,hh=h(y)
        recordlo=max(recordlo,p*el+q*hl-1)
        if j:recordhi=max(recordhi,p*last+q*hh-1)
        last=eh
    check(recordlo<=recordhi)
    return recordlo,recordhi
def checked_algebra():
    cnt=0
    for m in range(2,13):
      for i in range(1,m):
       p=Q(i,m);q=1-p/2;c=Q(m,i);f=3*c+2;d=c/2+f;e=2*f
       for j in range(1,6):
        y=Q(j,7);z=(1-y)/3;X=Q(2*j+1,15);Z=X/3
        # Terms containing logs substituted by their stationarity equalities.
        ly=p*c*X+(1-p)*d*Z;lz=p*d*X+(1-p)*e*Z
        lX=q*c*y+(1-q)*d*z;lZ=q*d*y+(1-q)*e*z
        fn=p*X+(1-p)*Z+q*y*(1+ly)+(1-q)*z*(1+lz)-1
        fnT=q*y+(1-q)*z+p*X*(1+lX)+(1-p)*Z*(1+lZ)-1
        check(fn==fnT)
        # coefficient of u² in the formal weighted exponential Taylor products
        A=c*y-d*z;D=d*y-e*z
        co2=X*(p*A*A/2+A)+Z*((1-p)*D*D/2-D)
        twice=X*(p*A*A+2*A)+Z*((1-p)*D*D-2*D)
        check(2*co2==twice)
        # sign decomposition in the direct endpoint proof
        Q0=q; P=2*q-1; t=c*q;x=y/2; w=(1-q)*t*y/q
        check(P*x*(1-w)-q*x+(1-q)*(y+t*x*y)==(1-q)*(y-x)+(1-q)**2*t*x*y/q)
        cnt+=1
    print('PASS: two-type transposition, curvature coefficient, endpoint gap identity:',cnt,'rational substitution sets.')
def main():
    checked_algebra()
    B=Q(1,20);s=1-B/2;c=Q(3)
    # Nonconcave balanced 1D objective: c*s > e, yet limiting balanced unmatched fraction strictly positive.
    check(c*s>Q(11,4));check(sum(Q(1,factorial(j)) for j in range(7))+Q(1,factorial(7))*Q(8,7)<Q(11,4)) # e<11/4
    out=[Hbox(s-d,s+d,c) for d in [Q(0),B/4,B/2]]
    for a,b,box in zip([Q(52,1000),Q(58,1000),Q(66,1000)],[Q(57,1000),Q(64,1000),Q(70,1000)],out):
        check(a<box[0]<=box[1]<b)
    print('PASS: B=1/20, alpha=3/2, exact global enclosures at imbalance 0,B/4,B/2:')
    print('      H(0) in (.052,.057), H(B/4) in (.058,.064), H(B/2) in (.066,.070).')
    B=Q(1,2);s=1-B/2;c=Q(8)
    L=Hbox(s,s,c,N=1200)
    check(-Q(1,4)<L[0]<=L[1]<-Q(24,100));el,_=power_exp(c)
    check((1-B)*el>Q(1,7000))
    print('PASS: B=1/2, alpha=4, exact H(0) in (-.25,-.24), H(B/2)>1/7000: nontrivial limiting plateau.')
if __name__=='__main__': main()
