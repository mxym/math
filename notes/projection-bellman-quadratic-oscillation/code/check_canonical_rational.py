#!/usr/bin/env python3
"""Standalone exact rational-interval reproduction of the canonical nonanalytic
T5-continuation Bellman profile's product-closure counterexample.

No Sage, Arb, floats, random choices, or external dependencies. Every step
uses integer/Fraction interval arithmetic with outward dyadic rounding.
The sole analytic Gamma input is the elementary sign-controlled Binet-Stirling
remainder (proved in the paper from Binet's positive-kernel integral).
"""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt,comb

GRID=2**136
TERMS=25
J=20


def need(b,msg):
    if not b:raise RuntimeError('canonical rational checker: '+msg)


def floor_grid(x):return F((x.numerator*GRID)//x.denominator,GRID)
def ceil_grid(x):return -floor_grid(-x)


class I:
    def __init__(self,lo,hi=None):
        lo=F(lo);hi=lo if hi is None else F(hi)
        need(lo<=hi,'invalid interval endpoints')
        self.lo,self.hi=floor_grid(lo),ceil_grid(hi)

    @staticmethod
    def c(o):return o if isinstance(o,I) else I(o)

    def __add__(a,b):
        b=I.c(b)
        return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-I.c(b)
    def __rsub__(a,b):return I.c(b)+-a
    def __mul__(a,b):
        b=I.c(b)
        c=[x*y for x in (a.lo,a.hi) for y in (b.lo,b.hi)]
        return I(min(c),max(c))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I.c(b)
        need(b.lo>0 or b.hi<0,'interval division by zero')
        return a*I(F(1,b.hi),F(1,b.lo))
    def __rtruediv__(a,b):return I.c(b)/a
    def __pow__(a,n):
        need(type(n) is int,'fractional powers must use sqrt enclosure')
        if n<0:return I(1)/a**(-n)
        if n==0:return I(1)
        if n%2==0 and a.lo<0<a.hi:
            return I(0,max(abs(a.lo),abs(a.hi))**n)
        if n%2==0 and a.hi<=0:return I(a.hi**n,a.lo**n)
        return I(a.lo**n,a.hi**n)
    def sqrt(a):
        need(a.lo>0,'square-root domain not positive')
        n=a.lo.numerator*GRID*GRID//a.lo.denominator
        low=isqrt(n)
        m=(a.hi.numerator*GRID*GRID+a.hi.denominator-1)//a.hi.denominator
        high=isqrt(m)
        if high*high<m:high+=1
        return I(F(low,GRID),F(high,GRID))
    def log(a):
        need(a.lo>0,'logarithm domain not positive')
        ll,_=log_point(a.lo)
        _,hh=log_point(a.hi)
        return I(ll,hh)
    def __repr__(a):
        return f'I([{a.lo},{a.hi}])' # purely rational diagnostic


@lru_cache(maxsize=None)
def log2_pair():
    # 2*atanh(1/3) = log 2 exactly, without recursive normalization.
    z=F(1,3);power=z;S=F(0)
    for j in range(TERMS):
        S+=2*power/F(2*j+1)
        power*=z*z
    err=2*power/(F(2*TERMS+1)*(1-z*z))
    return S,S+err


def log_atanh(x):
    x=F(x)
    need(x>0,'log point domain')
    shift=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/F(2**shift) if shift>=0 else x*F(2**(-shift))
    if y<1:y*=2;shift-=1
    elif y>=2:y/=2;shift+=1
    z=(y-1)/(y+1)
    power=z;S=F(0)
    for i in range(TERMS):
        S+=2*power/F(2*i+1)
        power*=z*z
    tail=F(2)*power/(F(2*TERMS+1)*(1-z*z))
    if shift==0:return S,S+tail
    lo2,hi2=log2_pair()
    if shift>0:return S+shift*lo2,S+tail+shift*hi2
    return S+shift*hi2,S+tail+shift*lo2


@lru_cache(maxsize=4096)
def log_point(x):return log_atanh(F(x))


def atan_pair(z,N):
    z=F(z);need(0<z<1 and N%2==0,'alternating arctan domain')
    S=sum((-1)**k*z**(2*k+1)/F(2*k+1) for k in range(N))
    return S,S+z**(2*N+1)/F(2*N+1)


def pi_interval():
    a,b=atan_pair(F(1,5),32)
    c,d=atan_pair(F(1,239),10)
    p=I(16*a-4*d,16*b-4*c)
    need(p.lo>F(333,106) and p.hi<F(355,113),'Machin pi bracket false')
    return p

PI=pi_interval()


# B2=1/6, B4=-1/30, B6=1/42, B8=-1/30, B10=5/66.
B_LIST=(F(1,6),-F(1,30),F(1,42),-F(1,30))
B10=F(5,66)


def log_C_interval(x):
    # Exact Gamma duplication: C(x)=Gamma(x+1/2)/(sqrt(pi)Gamma(x+1)).
    # Binet's positive-kernel formula, after four Stirling correction terms,
    # has 0<R_5(z)<B10/[10*9*z^9] for every real z>0.
    # Hence -2R_5(x)+R_5(2x) is bracketed by exact terms below.
    x=I.c(x)
    need(x.lo>0,'central-binomial Gamma ratio domain')
    corr=I(0)
    for k,B in enumerate(B_LIST,1):
        p=2*k
        beta=-(F(2)-F(1,2**(p-1)))*B/F(p*(p-1))
        corr+=I(beta)/(x**(p-1))
    rem=I(B10/F(90))
    remainder=I(-2)*rem/x**9
    remainder_hi=rem/(I(2)*x)**9
    # A lower/upper envelope for the omitted correction.
    lower=I(remainder.lo)
    upper=I(remainder_hi.hi)
    correction=corr+I(lower.lo,upper.hi)
    return -(PI*x).log()/2+correction


def G_interval(d):
    d=I.c(d)
    need(d.lo>0,'G requires positive real input')
    total=I(F(2,9))*I(2).log()
    for j in range(J):
        dj=((I(3)*d+1)*4**j-1)/3
        total+=I(F(2,4**(j+1)))*log_C_interval(dj)
    m=F(1,4**J)
    S0=F(2,3)*m
    S1=m*(F(2*J,3)+F(2,9))
    # For dj>=d*4^j and dj+1/2<=(d+1/2)*4^j, and Gamma logconvexity
    # 1/sqrt(pi*(x+1/2))<C(x)<1/sqrt(pi*x), j>=J.
    tail_lo= -(I(S0)*(PI*(d+F(1,2))).log()+I(S1)*I(4).log())/2
    tail_hi= -(I(S0)*(PI*d).log()+I(S1)*I(4).log())/2
    need(tail_lo.hi<=tail_hi.lo,'infinite tail lower/upper ordering failed')
    return total+I(tail_lo.lo,tail_hi.hi)


def canonical_psi(t,c):
    t=I.c(t)
    need(0<t.lo and t.hi<=1,'profile argument outside (0,1]')
    u=I(16)*t/(9+(81-32*t*t).sqrt())
    w=u*u
    d=(16-w)/(3*w)
    h=6/u
    A=I(F(2,3))*(c+h.log())+G_interval(d)
    return (3*w/(16+2*w))*A


def check():
    c=(I(F(2,3))*I(6).log()+G_interval(I(5)))/I(F(16,3))
    need(c.lo>F(4853,100000) and c.hi<F(4854,100000),
         'binary-T5 c-star enclosure invalid')
    r=8;h=F(53,7)
    need(h==F(18,7)+5,'explicit actual polytope H not reproducible')
    p0=canonical_psi(I(h)/I(r+1),c)
    p1=canonical_psi(I(h)/I(2*r+1),c)
    M=I(h)*I(F(comb(2*r,r),4**r))
    slack=-c-I(2*r+1)*p1+I(2*r+2)*p0-M.log()
    need(slack.hi < -F(1,20000),
         'canonical profile product-closure violation not rigorously established')
    print('PASS: pure-rational-interval certification of canonical nonanalytic profile failure')
    print('attained K=(T1 x T2)*point^(*5), (d,H)=(8,53/7)')
    print('strict Phi(K x K)-2Phi(K)-log multiplier < -1/20000')
    print('Gamma log bounds: four Stirling/Bernoulli terms and signed Binet remainder')
    print('G infinite tail: exact geometric bounds via Gamma log-convexity')
    print('number of certified G summands =',J)
    print('pure Python int/Fraction 136-bit dyadic intervals, no Sage or Arb needed')
    print('the theorem excludes only this canonical orbit interpolant, not every sharp profile')


if __name__=='__main__':check()
