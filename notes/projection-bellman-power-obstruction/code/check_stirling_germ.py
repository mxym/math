#!/usr/bin/env python3
"""Exact rational checks for the formal Stirling-germ nonanalyticity proof.

The ALL-ORDERS conclusion in paper.md relies on classical Stirling/Euler-
Maclaurin asymptotics and Euler's exact Bernoulli-zeta formula. This finite
program independently checks coefficients and rational composition data;
it does not treat a finite prefix as evidence for formal divergence.
"""
from fractions import Fraction as F
from math import comb, factorial


def need(cond,msg):
    if not cond:raise RuntimeError('Stirling-germ checker: '+msg)


def bernoulli(N):
    # Derives B_n from sum_{k=0}^n binom(n+1,k) B_k = 0 (n>=1).
    B=[F(1)]
    for n in range(1,N+1):
        B.append(-sum(F(comb(n+1,k))*B[k] for k in range(n))/F(n+1))
    return B


def beta(k,B):
    p=2*k
    # log binom(2d,d)/4^d + .5 log(pi*d)
    return -(F(2)-F(1,2**(p-1)))*B[p]/F(p*(p-1))


def test():
    N=16
    B=bernoulli(2*N)
    expect=[-F(1,8),F(1,192),-F(1,640),F(17,14336)]
    vals=[beta(k,B) for k in range(1,N+1)]
    need(vals[:4]==expect,'central-binomial formal series initial coefficients incorrect')
    # Euler's exact formula: |B_(2k)|=2(2k)! zeta(2k)/(2pi)^(2k).
    # With zeta>1, 2-2^(1-2k)>1 and pi<22/7, one gets the
    # STRICT rational lower bound displayed in the proof.
    for k,b in enumerate(vals,1):
        lower=F(2*factorial(2*k-2))*F(7,44)**(2*k)
        need(abs(b)>lower,f'Bernoulli-factorial coefficient lower bound failed k={k}')
        need((b>0)==(k%2==0),'Bernoulli coefficient sign pattern failed')
    for v in (F(1,10),F(1,100),F(1,1000)):
        w=16*v/(3+v)
        need(3*w/(16-w)==v,'analytic variable change not invertible')
        need(w>0,'positive substitution cannot be negative')
    # Binary T5 orbit coordinate change, exact integer identities.
    for j in range(13):
        u=F(1,2**j);w=u*u
        d=(16-w)/(3*w)
        H=6/u
        D=d+1
        t=H/D
        need(d.denominator==1 and d==(16*4**j-1)//3,
             'binary T5 dimension substitution incorrect')
        need(t==9*u/(8+u*u),'quadratic parameter substitution incorrect')
        need(F(1,d)==3*w/(16-w),
             'binary orbit reciprocal substitution is incorrect')
    print('PASS: exact Stirling-germ rational coefficients and analytic variable change')
    print('first four formal coefficients =',','.join(str(x) for x in vals[:4]))
    print('positive Bernoulli/Euler factorial lower bounds checked for k=1..',N)
    print('formal sign alternation and inverse substitution checked exactly')
    print('binary T5 orbit square-root/reciprocal substitutions checked for 13 levels')
    print('infinite nonanalyticity theorem uses all-orders Euler-Maclaurin & Euler zeta formula')


if __name__=='__main__':test()
