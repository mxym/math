#!/usr/bin/env python3
"""Exact finite checks underlying the standalone binary hashing asymptotics."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb


def transposed(rows,y):
    x=0
    for i,r in enumerate(rows):
        if (y>>i)&1:
            x ^= r
    return x


def char(y,z):
    return (-1)**((y&z).bit_count()%2)


def image(rows,x):
    return sum(((r&x).bit_count()%2)<<i for i,r in enumerate(rows))


def fourier_and_pairwise():
    fourier_checks,pair_checks=0,0
    for n,k in ((2,1),(2,2),(3,2),(3,3),(4,2),(4,3)):
        K=1<<k
        pairs=list(combinations(range(1,K),2))
        histogram=[{} for _ in pairs]
        exact_low_sum=F(0)
        good_low_sum=F(0)
        low_count=0
        for rows in product(range(1<<n),repeat=k):
            raw=[0]*K
            for x in range(1<<n):
                raw[image(rows,x)]+=3**(n-x.bit_count())
            W=[transposed(rows,y).bit_count() for y in range(K)]
            Fv=[sum(F(char(y,z),2**W[y]) for y in range(1,K)) for z in range(K)]
            assert all(F(raw[z]*K,4**n)-1==Fv[z] for z in range(K))
            assert sum(f*f for f in Fv)/K == sum(F(1,4**j) for j in W[1:])
            tv=sum(abs(f) for f in Fv)/(2*K)
            assert tv>=max(F(1,2**(j+1)) for j in W[1:])
            fourier_checks+=K
            for (y,z),h in zip(pairs,histogram):
                coord=(W[y],W[z])
                h[coord]=h.get(coord,0)+1
            low=[j for j in W[1:] if j<=1]
            low_count+=len(low)
            amp=sum((F(1,2**j) for j in low),F(0))
            exact_low_sum+=amp
            if len(low)==1:
                assert tv>=amp/2
                good_low_sum+=amp
        N=2**(n*k)
        assert good_low_sum >= (1-F(low_count,N))*exact_low_sum
        for h in histogram:
            assert all(4**n*h.get((u,v),0)==N*comb(n,u)*comb(n,v)
                       for u,v in product(range(n+1),repeat=2))
            pair_checks+=(n+1)**2
    return fourier_checks,pair_checks


def sign_moments():
    tests=0
    # A set with one long relation acts as independent signs for moments
    # below that relation's length, but not for every moment.
    for d in range(2,7):
        mags=[F(i+2,4**i) for i in range(d+1)]
        indep=list(1<<i for i in range(d+1))
        relation=indep[:d]+[(1<<d)-1]
        for order in range(1,d+1):
            x=F(sum(sum(a*char(y,z) for a,y in zip(mags,indep))**order
                    for z in range(1<<(d+1))),1<<(d+1))
            y=F(sum(sum(a*char(w,z) for a,w in zip(mags,relation))**order
                    for z in range(1<<d)),1<<d)
            assert x==y
            tests+=1
        assert sum(F(product_sign(relation,z),1<<d) for z in range(1<<d))==1
        assert sum(F(product_sign(indep,z),1<<(d+1)) for z in range(1<<(d+1)))==0
    return tests


def product_sign(words,z):
    p=1
    for w in words:
        p*=char(w,z)
    return p


def binomial_tilts():
    tests=0
    for n,a in product(range(1,19),(F(1,8),F(2,5),F(1,2),F(4,5))):
        for r in (1,2):
            b=a**r
            q=b/(1+b)
            for w in range(n+1):
                allowed=range(w+1) if r==1 else range(w,n+1)
                exp=sum(comb(n,j)*b**j for j in allowed)
                got=(1+b)**n*sum(comb(n,j)*q**j*(1-q)**(n-j) for j in allowed)
                assert exp==got
                tests+=1
    return tests


def main():
    print("PASS exact Fourier rows and joint pair counts:",fourier_and_pairwise())
    print("PASS fixed-order sign moments across a longer relation:",sign_moments())
    print("PASS exact first/second-moment binomial tilts:",binomial_tilts())


if __name__=="__main__":
    main()
