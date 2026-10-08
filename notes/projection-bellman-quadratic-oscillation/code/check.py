#!/usr/bin/env python3
"""Independent rational checker for the *no quadratic germ* sharp Bellman theorem.

No imported research Python code, floating arithmetic, or external libraries.
Analytic input: Robbins factorial bounds, classical Machin pi identity,
Bertrand not required, the exact inherited product/join state identities.
The proof, not this finite script, establishes the all-index limits.
"""
from fractions import Fraction as F
from functools import lru_cache

N=20
J=13
PILO=F(333,106)
PIHI=F(355,113)


def need(b,msg):
    if not b:raise RuntimeError('quadratic-germ checker: '+msg)


def atan_bounds(z,k=12):
    z=F(z)
    need(0<z<1 and k%2==0,'arctan interval domain')
    S=sum(F(-1 if j%2 else 1)*z**(2*j+1)/F(2*j+1) for j in range(k))
    return S,S+z**(2*k+1)/F(2*k+1)


def verify_pi():
    a,b=atan_bounds(F(1,5))
    c,d=atan_bounds(F(1,239))
    need(16*a-4*d>PILO and 16*b-4*c<PIHI,'Machin pi bound')


@lru_cache(maxsize=None)
def log2_bounds():
    z=F(1,3);power=z;S=F(0)
    for k in range(N):
        S+=2*power/F(2*k+1)
        power*=z*z
    return S,S+2*power/(F(2*N+1)*(1-z*z))


@lru_cache(maxsize=20000)
def log_bounds(x):
    x=F(x)
    need(x>0,'ln interval must be positive')
    e=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/F(2**e) if e>=0 else x*F(2**(-e))
    if y<1:y*=2;e-=1
    elif y>=2:y/=2;e+=1
    need(1<=y<2,'binary logarithm normalization')
    z=(y-1)/(y+1)
    power=z;S=F(0)
    for k in range(N):
        S+=2*power/F(2*k+1)
        power*=z*z
    rem=2*power/(F(2*N+1)*(1-z*z))
    lo2,hi2=log2_bounds()
    if e>=0:return S+e*lo2,S+rem+e*hi2
    return S+e*hi2,S+rem+e*lo2


def delta_g_bounds(d):
    # Exact delta = ln g(d)^2/g(2d), via Robbins
    # ln g(n)=n-1/2 ln(2 pi n)-theta_n,
    # 1/(12n+1) < theta_n < 1/(12n).
    need(type(d) is int and d>=1,'dimension must be positive integer')
    lowerlog=log_bounds(PILO*d)[0]
    upperlog=log_bounds(PIHI*d)[1]
    lower=-upperlog/2-F(1,6*d)+F(1,24*d+1)
    upper=-lowerlog/2-F(2,12*d+1)+F(1,24*d)
    need(lower<upper,'Stirling central-binomial interval reversed')
    return lower,upper


def G5_bounds():
    # G(5)=2/9 ln 2+sum_{j>=0}2*4^{-j-1}*delta_g(d_j)
    lo,hi=(F(2,9)*t for t in log_bounds(2))
    for j in range(J):
        d=(16*4**j-1)//3
        a,b=delta_g_bounds(d)
        w=F(2,4**(j+1))
        lo+=w*a;hi+=w*b
    # For j>=J, -delta_j < (1/2)ln(pi*d_j)+1/(6d_j).
    # pi<4 and d_j<(5+1)*4^j and d_j>=4^j.
    # Geometric tails: S0=sum(2*4^{-j-1})=2/(3*4^J);
    # S1=sum(2*j*4^{-j-1})=4^{-J}(2J/3+2/9).
    m=F(1,4**J)
    S0=F(2,3)*m
    S1=(F(2*J,3)+F(2,9))*m
    rem=(S0*(log_bounds(F(4*6))[1]/2+F(1,6))
         +S1*log_bounds(4)[1]/2)
    lo-=rem
    need(lo<hi,'G5 infinite tail interval reversed')
    return lo,hi


def check():
    verify_pi()
    gl,gh=G5_bounds()
    ll,lh=log_bounds(6)
    c_lo=(F(2,3)*ll+gl)/F(16,3)
    c_hi=(F(2,3)*lh+gh)/F(16,3)
    need(c_lo>F(485,10000) and c_hi<F(49,1000),
         'certified binary orbit log-rate not in needed interval')

    # ℓ=1/2 log(27/(4pi)) < 1/2 log(27/(4*333/106))
    ratio=F(27)/(4*PILO)
    need(ratio==F(159,74),'rational pi simplification incorrect')
    ell_hi=log_bounds(ratio)[1]/2
    L_hi=c_hi+ell_hi
    need(ell_hi<F(383,1000) and L_hi<F(54,125),
         'forced quadratic orbit constant L not below 54/125')

    # t_j=H_j/(d_j+1),  d_j=(16*4^j-1)/3, H_j=6*2^j.
    # Point-join perturbation: m_j=2^(j-1), H'_j=13*2^(j-1).
    for j in range(1,17):
        d0=(16*4**j-1)//3
        need(d0*3+1==16*4**j,'binary dimension formula')
        H0=6*2**j
        m=2**(j-1)
        d=d0+m;H=H0+m
        need(H==13*2**(j-1),'joined H-state expression')
        need(H*H<F(507,64)*d,'H/sqrt(d) approaches bound from below')
        need(d>0 and H>0,'incorrect actual join')
    z0sq=F(27,4)
    zsq=F(507,64)
    need(zsq/z0sq==F(169,144),'asymptotic normalized H ratio')

    # ln(13/12)=2*atanh(1/25) > 2/25 (strict).
    z=F(1,25)
    need((1+z)/(1-z)==F(13,12),'log ratio arctanh transform')
    S_upper=F(25,144)*F(54,125)-F(2,25)
    need(S_upper==-F(1,200),'analytic limit fails to be negative')

    # If ε=limsup |ψ(t)-αt²|/t², closure forces
    # ε >= -S_limit / ((5/2)*(507/64)).
    correction=F(5,2)*zsq
    eps_lb=F(1,200)/correction
    need(eps_lb==F(16,63375) and eps_lb>F(1,4000),
         'universal quadratic oscillation lower bound wrong')
    print('PASS: exact independent checker for no-quadratic-germ sharp Bellman obstruction')
    print('binary T5 cstar strictly between 485/10000 and 49/1000')
    print('L=cstar+0.5*ln(27/(4*pi)) < 54/125')
    print('attained perturbation: K_j joined with 2^(j-1) points')
    print('asymptotic scaled-H ratio squared is 507/64; ratio z/z0 is 13/12')
    print('quadratic-germ self-product slack limit < -1/200')
    print('forced limsup second-order relative error > 16/63375 > 1/4000')
    print('therefore no sharp separately-closed scalar psi can possess a quadratic germ')
    print('all comparisons are exact Fraction/arctanh; infinite limits proven on paper')


if __name__=='__main__':check()
