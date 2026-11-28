#!/usr/bin/env python3
"""Exact finite constants for CGFHSOPStrictEntropyUpper.md; no floating point."""
from fractions import Fraction as F
from math import factorial

def require(test, msg):
    if not test:
        raise AssertionError(msg)

def exp_lower(x, k):
    return sum(x**i / factorial(i) for i in range(k+1))

def exp_upper(x, k):
    return exp_lower(x,k) + x**(k+1)/factorial(k+1)/(1-x/(k+2))

require(exp_lower(F(9,10),8) > F(1000,407), "larger-decay geometric bound")
require(exp_lower(F(9,20),8) > F(1000,638), "tail-decay geometric bound")
require(exp_upper(F(4),24) < 55, "bound for exp(4)")
require(exp_upper(F(1,2),10) < F(5,3), "bound for exp(1/2)")
require(2+2*F(5,2)*F(17,12)*F(89,80)*F(5,3) < 16, "totient counting constant")

M,K,S=4096,96,2**72
phi=list(range(M))
primes=[]
for p in range(2,M):
    if phi[p]==p:
        primes.append(p)
        for k in range(p,M,p):
            phi[k] -= phi[k]//p

def rounded_upper_powers(numer):
    t=[S]
    for j in range(M):
        t.append((t[-1]*numer+999)//1000)
    return t

def outward_tail(powers):
    # For j>=4096, phi(j)>=128(1+i/2) on the i-th dyadic block.
    return M*F(powers[128], S)/(1-2*F(powers[64],S))

g=rounded_upper_powers(407)
lower=S
for n in range(1,M):
    lower=lower*(S-g[phi[n]])//S
p0=F(lower,S)*(1-outward_tail(g))/55
require(p0>F(1,320), "uniform isolated pattern")
g=rounded_upper_powers(638)
tail=F(sum(g[phi[n]] for n in range(K+1,M)),S)+outward_tail(g)
require(tail<F(9,409600), "tail repair cost")
density=F(1)
for p in primes:
    if p<=K: density *= F(p-1,p)
require(density*(1-F(10,K))>F(1,10), "density of admissible test roots")
require(F(9,320)*F(1,320)/40==F(9,4096000), "final exponential gain")

# Independent finite controls for the local obstruction and overlap mechanism.
def mobius(k):
    r=1
    for p in primes:
        if p*p>k: break
        if k%p==0:
            k//=p
            if k%p==0:return 0
            r=-r
    if k>1:r=-r
    return r

counts=[0,0]
for X in [20, 200, 5000]:
    R=[r for r in range(X,2*X+1) if all(r%p for p in primes if p<=K)]
    roots={}
    for r in R:
        for k in range(1,K+1):
            m=r*k
            require(m not in roots, "independence of short multiples")
            roots[m]=r
            counts[0]+=1
        for extra in [(), (5,7,11), (2*r+1,4*r+1,6*r+1)]:
            # Under the isolated pattern the only exponent on an r-multiple is e_6r=1.
            E=(6*r,)+tuple(m for m in extra if m%r)
            numerator=[];denominator=[]
            for m in range(r,6*r+1,r):
                net=sum(mobius(j//m) for j in E if j%m==0)
                if net>0:numerator += [m]*net
                if net<0:denominator += [m]*(-net)
            require(numerator==[r,6*r] and denominator==[2*r,3*r],"canonical local pattern")
            gains={a*2*r+b*3*r for a in range(4) for b in range(3)}
            require(sum(m in gains for m in numerator)==1,"Hall-type obstruction")
            counts[1]+=1
print(f"PASS: exact density, probability and tail bounds; {counts[0]} short-multiple and {counts[1]} obstruction controls")
