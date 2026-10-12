#!/usr/bin/env python3
"""Rational interval proof: exact T5 binary-tail functional is not join-superadditive.

This rules out a second tempting shortcut to a sharp global Bellman envelope.
It is not a counterexample to the claimed optimality of the T5 orbit itself.
"""
from fractions import Fraction as F
from check import log_bounds,require

PI_LO=F(333,106)
PI_HI=F(355,113)
LEVELS=12


def atan_interval(z,N=12):
    require(z>0 and z<1 and N%2==0,'atan interval domain')
    S=sum((-1)**j*z**(2*j+1)/F(2*j+1) for j in range(N))
    return S,S+z**(2*N+1)/F(2*N+1)


def pi_check():
    a,b=atan_interval(F(1,5))
    c,d=atan_interval(F(1,239))
    require(PI_LO<16*a-4*d and 16*b-4*c<PI_HI,
            'Machin pi enclosure not verified')


def diff_bounds(d):
    # Robbins: ln g(d)=d-.5 ln(2 pi d)-theta_d,
    #            1/(12d+1)<theta_d<1/(12d).
    # ln(g(d)^2/g(2d))=-.5 ln(pi d)-2theta_d+theta_(2d).
    LL=log_bounds(PI_LO*d)[0]
    UU=log_bounds(PI_HI*d)[1]
    lo=-UU/2-F(1,6*d)+F(1,24*d+1)
    hi=-LL/2-F(2,12*d+1)+F(1,24*d)
    require(lo<=hi and hi<0,'invalid central binomial Robbins interval')
    return lo,hi


def G_bounds(d,J=LEVELS):
    lo,hi=[F(2,9)*v for v in log_bounds(2)]
    for j in range(J):
        dj=((3*d+1)*4**j-1)//3
        a,b=diff_bounds(dj)
        w=F(2,4**(j+1))
        lo+=w*a;hi+=w*b
    # For every omitted j, 0 > diff(d_j) > -(.5 ln(pi d_j)+1/(6d_j)).
    # The upper bound |diff| uses d_j <= (d+1)4^j and pi<4.
    A=log_bounds(4*(d+1))[1]
    ln4=2*log_bounds(2)[1]
    rem=F(2,4**J)*((A/2+F(1,6))/3+ln4/F(2)*(F(J,3)+F(1,9)))
    lo-=rem  # missing negative tail
    require(lo<=hi,'incorrect G interval')
    return lo,hi


def check():
    pi_check()
    g3=G_bounds(3);g5=G_bounds(5);g7=G_bounds(7)
    log6=log_bounds(6)
    c_lo=(F(2,3)*log6[0]+g5[0])/F(16,3)
    c_hi=(F(2,3)*log6[1]+g5[1])/F(16,3)
    require(c_lo>F(485,10000) and c_hi<F(486,10000),
            'certified sharp binary orbit log-rate enclosure failed')
    # Any continuous homogeneous sharp potential with a quadratic germ
    # at t=0 must have alpha=8/81*(c_*+1/2 ln(27/(4 pi))).
    Llo=log_bounds(F(27)/(4*PI_HI))[0]/2
    Lhi=log_bounds(F(27)/(4*PI_LO))[1]/2
    alpha_lo=F(8,81)*(c_lo+Llo)
    alpha_hi=F(8,81)*(c_hi+Lhi)
    require(F(4256,100000)<alpha_lo and alpha_hi<F(4257,100000),
            'exact orbit-imposed quadratic-germ interval not certified')

    # For B(d,h)=c(d+1/3)-(2/3)ln h-G(d), with c=the binary T5 rate:
    # S=B(7,36/7)-2B(3,18/7)
    #  =(2/3)c+(2/3)ln(9/7)+2G(3)-G(7).
    logratio=log_bounds(F(9,7))
    Slo=F(2,3)*(c_lo+logratio[0])+2*g3[0]-g7[1]
    Shi=F(2,3)*(c_hi+logratio[1])+2*g3[1]-g7[0]
    require(Shi< -F(3,10),
            'claimed failure of join superadditivity is not certified')
    print('PASS: exact binary-tail value-function candidate is NOT join-superadditive')
    print('geometrically attainable counterexample: T1 x T2 has (d,H,Q)=(3,18/7,28/27)')
    print('join defect: B(7,36/7)-2 B(3,18/7) < -3/10')
    print('pi, factorial correction, logarithm and infinite series tails rigorously enclosed')
    print('all continuous sharp join/product Bellman potentials must interpolate every T5 orbit state')
    print('if quadratic at t=0, its curvature alpha is strictly between 4256/100000 and 4257/100000')
    print('does not disprove the binary T5 global optimum conjecture')


if __name__=='__main__':check()
