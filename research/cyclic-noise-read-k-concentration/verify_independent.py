#!/usr/bin/env python3
from fractions import Fraction as F
from math import comb
from random import Random

def spectrum(n, supports, rates, I):
    m=len(I)
    g=tuple(tuple(sum(((i-a)%n in T)<<a for a in range(n)) for T in supports)
            for i in I)
    spectrum=[]
    for mask in range(1<<m):
        coefficients=[0]*len(supports)
        for ii in range(m):
            if (mask>>ii)&1:
                coefficients=[a^b for a,b in zip(coefficients,g[ii])]
        chi=F(1)
        for x,rate in zip(coefficients,rates):
            chi*=(1-2*rate)**x.bit_count()
        spectrum.append(chi)
    transformed=spectrum[:]
    for bit in range(m):
        width=1<<bit
        for start in range(0,1<<m,width*2):
            for idx in range(start,start+width):
                a,b=transformed[idx],transformed[idx+width]
                transformed[idx],transformed[idx+width]=a+b,a-b
    counts=[F(0)]*(m+1)
    for out,mass in enumerate(transformed):
        assert mass>=0
        counts[out.bit_count()]+=mass/(1<<m)
    return counts, spectrum

def test(n,T,rates,I):
    w,character=spectrum(n,T,rates,I)
    m=len(I)
    if not m:
        assert w==[1]
        return 0
    # Derive mean from singleton characters, read bound from column counts
    p=F(1,2)*(1-character[1])
    assert all((1-character[1<<i])/2==p for i in range(m))
    assert sum(w)==1 and sum(a*b for a,b in enumerate(w))==m*p
    k=max(sum(int((i-offset)%n in block) for i in I)
          for offset in range(n) for block in T)
    if k==0 or p in (0,1):
        assert w[int(m*p)]==1
        return 0
    checked=0
    for theta in (F(1,5),F(5),F(1,2),F(3,2)):
        scaled=sum(coef*theta**a for a,coef in enumerate(w))
        assert scaled**k <= (1+p*(theta**k-1))**m
        checked+=1
    # Form the KL threshold as ratios of Bernoulli point probabilities.
    for b in range(m+1):
        q=F(b,m)
        threshold=p**b*(1-p)**(m-b)/(q**b*(1-q)**(m-b))
        if q<=p:
            assert sum(w[:b+1])**k<=threshold
            checked+=1
        if q>=p:
            assert sum(w[b:])**k<=threshold
            checked+=1
    return checked

rng=Random(91831)
checks=0
for _ in range(160):
    n=rng.randint(1,7)
    blocks=rng.randint(1,4)
    supports=tuple(frozenset(i for i in range(n) if rng.randrange(2))
                   for _ in range(blocks))
    rates=tuple(rng.choice((F(0),F(1),F(1,2),F(1,7),F(3,5)))
                for _ in range(blocks))
    I=tuple(i for i in range(n) if rng.randrange(4))
    checks+=test(n,supports,rates,I)
n,k,r=12,4,3
T=(frozenset((0,3,6,9)),)
for ell in range(1,k+1):
    I=tuple(range(ell*r))
    w,C=spectrum(n,T,(F(1,6),),I)
    p=(1-C[1])/2
    law=[F(0)]*(ell*r+1)
    for j in range(r+1):
        law[ell*j]=comb(r,j)*p**j*(1-p)**(r-j)
    assert w==law
    if ell>1:
        assert w[-1] > p**len(I)
print(f"rational Fourier inversion: 160 seeded instances, {checks} exact comparisons")
print("independent subgroup certificates: 4 exact full/truncated laws PASS")
