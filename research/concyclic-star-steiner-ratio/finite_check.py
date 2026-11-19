"""Rational, fail-closed scalar estimates in FINITE.md; no trigonometric numerics.
Each interval lower bound rounds by endpoint monotonicity, not by sampling.
"""
from fractions import Fraction as F
def require(x, reason):
    if not x: raise RuntimeError(reason)
def atan_bound(q, n):
    s=sum((-1)**j*q**(2*j+1)/(2*j+1) for j in range(n))
    b=s+(-1)**n*q**(2*n+1)/(2*n+1)
    return min(s,b), max(s,b)
def k(v,u):
    return (3*v**3+6*v*v*u+4*v*u*u+2*u**3)/(5*(v+2*u))
def run():
    il,ih=atan_bound(F(1,5),8); jl,jh=atan_bound(F(1,239),4)
    lo,hi=F(31415,10000),F(31416,10000)
    require(lo<16*il-4*jh<16*ih-4*jl<hi,'Machin enclosure')
    atlo,_=atan_bound(F(1,9),2)
    require(hi/4-atlo<F(675,1000),'arctan(4/5) upper')
    su,au=F(141422,100000),F(32493,100000)
    sl=F(223606,100000)
    require(su**2>2 and sl**2<5 and (5-2*sl)/5 <au**2,'radical enclosures')
    del4,del5=F(1723,10000),F(108,1000)
    require(8*(su-1)-lo<del4 and 10*au-lo<del5,'regular errors')
    T=F(47,100); q=F(4,5); umax=F(83,200)
    require(lo*T*T/4>del4 and su-1<umax,'large t and tangent')
    def v(t):return F(118,100)-F(11,10)*t
    def tangent(t):return 2*(v(t)-F(675,1000)-(v(t)-q)/(1+q*q))
    require(tangent(T)>0 and v(T)>umax,'positive monotone lower')
    N=10000; worst5=1; worst4=1; worstk=1
    for j in range(N):
        a,b=F(j,N),F(j+1,N)
        g5=lo*a*a/4+lo**3/96*(1-b)**5/(1+b)-del5
        require(g5>0,'n>=5 cell '+str(j))
        worst5=min(worst5,g5)
        if b<=T:
            e=(1-b)/(1+b)-k(v(a),umax)
            h=lo*a*a/4+(1-b)**2/(1+b)*tangent(b)-del4
            require(e>0 and h>0,'n=4 cell '+str(j))
            worst4=min(worst4,h);worstk=min(worstk,e)
    print('PASS n>=5 all t: 10000 rational enclosures; minimum surplus >',int(worst5*10**6),'/10^6')
    print('PASS n=4 below 47/100: 4700 rational enclosures each; minimum k surplus >',int(worstk*10**6),'/10^6; cost surplus >',int(worst4*10**6),'/10^6')
    print('PASS Machin/trig/radical comparisons and n=4 t>=47/100')
if __name__=='__main__':run()
