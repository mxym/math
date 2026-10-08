#!/usr/bin/env sage -python
"""Rigorous 192-bit Arb-ball counterexample to the canonical nonanalytic
T5-orbit Bellman interpolation's separate product-closure inequality.

Requires SageMath with Arb RealBallField. Every checked inequality is an
interval comparison; no floating-point optimizer or heuristic acceptance.
The infinite G(d) series tail is enclosed analytically using strict Gamma
ratio bounds derived from log-convexity of Euler's Gamma function.
"""
from sage.all import RealBallField,QQ
from math import comb

R=RealBallField(192)
J=22
PI=R.pi()


def need(b,msg):
    if not b:raise RuntimeError('canonical profile Arb certificate: '+msg)


def central_binomial_log(d):
    # C(d)=Gamma(d+1/2)/(sqrt(pi)*Gamma(d+1)) for every real d>0.
    need(d>0,'Gamma ratio evaluated outside positive real axis')
    return (d+R(1)/2).log_gamma()-(d+1).log_gamma()-PI.log()/2


def G_interval(d):
    # Exact definition G(d)=2/9 log2 +sum_(j>=0) 2/4^(j+1) log C(d_j),
    # d_j=((3d+1)*4^j-1)/3. The first J terms use Arb certified loggamma.
    d=R(d)
    need(d>0,'G dimension must be positive')
    partial=R(2)/9*R(2).log()
    for j in range(J):
        dj=((3*d+1)*4**j-1)/3
        partial+=R(2)/4**(j+1)*central_binomial_log(dj)
    # Gamma log-convexity gives, for all real x>0,
    # 1/sqrt(pi*(x+1/2)) < C(x) < 1/sqrt(pi*x).
    # For every j>=0: d*4^j <=d_j; d_j+1/2 <=(d+1/2)*4^j.
    # Sum the two log bounds for the entire tail j>=J exactly.
    m=R(4)**(-J)
    S0=R(2)/3*m
    S1=m*(R(2)*J/3+R(2)/9)
    tail_lower=-(S0*(PI*(d+R(1)/2)).log()+S1*R(4).log())/2
    tail_upper=-(S0*(PI*d).log()+S1*R(4).log())/2
    need(tail_lower<tail_upper,'series tail interval order invalid')
    return partial+tail_lower,partial+tail_upper


def candidate_psi_interval(t,c_lower,c_upper):
    # t=9u/(8+u^2), u=16t/(9+sqrt(81-32t^2)), w=u^2.
    # Canonical A(w)=(2/3)(c+log(6/u))+G((16-w)/(3w)); psi=A/D.
    t=R(t)
    need(t>0 and t<=1,'Bellman shape parameter outside (0,1]')
    u=16*t/(9+(81-32*t*t).sqrt())
    w=u*u
    d=(16-w)/(3*w)
    h=6/u
    low,high=G_interval(d)
    scale=3*w/(16+2*w)
    return scale*(R(2)/3*(c_lower+h.log())+low),\
           scale*(R(2)/3*(c_upper+h.log())+high)


def replay():
    g5lo,g5hi=G_interval(R(5))
    D5=R(16)/3
    c_low=(R(2)/3*R(6).log()+g5lo)/D5
    c_hi=(R(2)/3*R(6).log()+g5hi)/D5
    need(c_low<R(QQ(49)/1000) and c_hi>R(QQ(48)/1000),
         'incorrect inherited binary orbit constant')
    need(c_low>R(QQ(4853)/100000) and c_hi<R(QQ(4854)/100000),
         'insufficient binary orbit rate enclosure')
    # Attainable K=(T1 x T2) * point^(*5) has r=8 and H=53/7.
    # From inherited exact calculus T1 x T2: d=3,H=18/7,Q=28/27.
    r=8
    h=R(QQ(53)/7)
    need(QQ(53)/7==QQ(18)/7+5,'explicit attainable H input invalid')
    low_0,hi_0=candidate_psi_interval(h/(r+1),c_low,c_hi)
    low_1,hi_1=candidate_psi_interval(h/(2*r+1),c_low,c_hi)
    # Exact product multiplier = H*binomial(2r,r)/4^r.
    M=h*R(QQ(comb(2*r,r))/4**r)
    # Phi_prod - 2 Phi_child - ln M
    # = -c -(2r+1)psi(h/(2r+1)) +2(r+1)psi(h/(r+1)) -ln M.
    slack_upper=-c_low-(2*r+1)*low_1+2*(r+1)*hi_0-M.log()
    slack_lower=-c_hi-(2*r+1)*hi_1+2*(r+1)*low_0-M.log()
    need(slack_lower<=slack_upper,'negative interval reversed')
    require_limit=-R(QQ(1)/20000)
    need(slack_upper<require_limit,
         'strict product-closure failure not separated from zero')
    print('PASS: certified canonical nonanalytic orbit interpolant fails product closure')
    print('geometrically attained input: K=(T1 x T2)*point^(*5), (d,H)=(8,53/7)')
    print('exact product case: K x K')
    print('Bellman product-closure slack strictly < -1/20000')
    print('all-order G-tail enclosed by gamma log-convexity and 22 Arb terms')
    print('proof arithmetic: 192-bit Sage/Arb real balls and exact rational endpoints')
    print('this does not disprove existence of a different sharp nonanalytic potential')


if __name__=='__main__':replay()
