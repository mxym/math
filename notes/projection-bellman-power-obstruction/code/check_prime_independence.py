#!/usr/bin/env python3
"""Replays finite triangular witnesses behind the all-index Bertrand argument.

The unbounded prime-existence theorem (Bertrand's postulate) is a named
classical mathematical input in paper.md; it is *not* inferred from this
finite computation. This checker uses exact integer trial division and
Legendre valuations only, no floats, random-prime APIs or assert controls.
"""
from math import isqrt

LEVELS=13


def need(ok,why):
    if not ok:raise RuntimeError('prime independence: '+why)


def isprime(n):
    if n<2:return False
    if n in (2,3):return True
    if n%2==0 or n%3==0:return False
    for q in range(5,isqrt(n)+1,6):
        if n%q==0 or n%(q+2)==0:return False
    return True


def factorial_valuation(n,p):
    v=0
    while n:
        n//=p
        v+=n
    return v


def binomial_valuation(d,p):
    return factorial_valuation(2*d,p)-2*factorial_valuation(d,p)


def multiplier_valuation(d,h,p):
    # M= h * binom(2d,d) / 4^d, with h=6*2^j.
    v=binomial_valuation(d,p)
    while h%p==0:
        h//=p
        v+=1
    if p==2:v-=2*d
    return v


def witness(levels=LEVELS):
    need(type(levels)==int and 1<=levels<=25,'invalid level count')
    data=[]
    for j in range(levels):
        d=(16*4**j-1)//3
        H=6*2**j
        need(3*d+1==16*4**j and d>0,'binary orbit dimension formula invalid')
        need(j==0 or d>2*data[-1][1], 'dimensions not sufficiently separated')
        p=next((z for z in range(d+1,2*d) if isprime(z)),None)
        need(p is not None,'missing prime witness in Bertrand interval')
        need(p>d and p<2*d and isprime(p),'invalid prime witness')
        need(multiplier_valuation(d,H,p)==1,'prime exponent of current multiplier not 1')
        for jj,dd,HH,pp in data:
            need(multiplier_valuation(dd,HH,p)==0,
                 f'new prime divides earlier multiplier at index {jj}')
        data.append((j,d,H,p))
    print('PASS: exact triangular prime-valuation witnesses for binary T5 orbit')
    print('tested orbit levels =',len(data))
    print('each new prime p_j satisfies d_j<p_j<2d_j and valuation v_(p_j)(M_j)=1')
    print('each prior M_i has valuation v_(p_j)(M_i)=0 (all i<j)')
    print('first four (j,d_j,H_j,p_j) =',data[:4])
    print('last  (j,d_j,H_j,p_j) =',data[-1])
    print('infinite theorem uses classical Bertrand postulate, not finite extrapolation')
    return data


if __name__=='__main__':witness()
