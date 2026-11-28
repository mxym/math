#!/usr/bin/env python3
from itertools import combinations
from fractions import Fraction
from math import factorial, gcd, isqrt

def primes_upto(n):
    a=[True]*(n+1)
    a[0]=a[1]=False
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=[False]*(((n-p*p)//p)+1)
    return [i for i,v in enumerate(a) if v]

PR=primes_upto(250)

def prod(xs):
    z=1
    for x in xs: z*=x
    return z

def geom(p,m):
    return (p**m-1)//(p-1)

def clog2(n):
    return (n-1).bit_length()

def threshold(A,u,m):
    target=u**m
    lo,hi=1,u
    while lo<hi:
        q=(lo+hi)//2
        if A*q**m>=target: hi=q
        else: lo=q+1
    return lo

def gmod(q,m,p):
    q%=p
    if q==1: return m%p
    return (pow(q,m,p)-1)*pow(q-1,-1,p)%p

statistic_cases=0
gap_recoveries=0
quotient_identities=0
for K in (4,5):
    c=(K-2).bit_length() # ceil(log2(K-1))
    L=factorial(K-2)
    for ps in combinations(PR[:9],K):
        u=prod(ps)
        for a in (1,2):
            n=u**a; M=clog2(n)
            J=L*((max(2,M*(M+c))+L-1)//L)
            m=a*J+1
            S=prod(geom(p,m) for p in ps)
            phiu=prod(p-1 for p in ps)
            A=u**m-phiu*S
            assert A==u**m-prod(p**m-1 for p in ps)
            assert u**m//ps[0]**m < A
            assert Fraction(A,u**m)<sum(Fraction(1,p**m) for p in ps)
            statistic_cases+=1
            if ps[1]*M >= ps[0]*(M+1):
                delta_num=(K-1)*ps[0]**m
                delta_den=ps[1]**m
                assert delta_num*(ps[0]-1)<=m*delta_den
                q=threshold(A,u,m)
                assert q==ps[0]
                gap_recoveries+=1
                for i in range(1,K-2):
                    mi=a*i*J+1
                    Si=prod(geom(p,mi) for p in ps)
                    Sip=Si//geom(ps[0],mi)
                    assert Sip==prod(geom(p,mi) for p in ps[1:])
                    quotient_identities+=1

gcd_scan_cases=0
proper_gcd_splits=0
proper_examples=[]
for ps in combinations(PR[:14],4):
    u=prod(ps)
    for m in range(2,19):
        d=1
        for p in ps:
            if any(gmod(q,m,p)==0 for q in ps if q!=p):
                d*=p
        gcd_scan_cases+=1
        if 1<d<u:
            proper_gcd_splits+=1
            if len(proper_examples)<8: proper_examples.append((ps,m,d))

failure_examples=[]
near=[p for p in PR if 90<=p<=180]
for ps in combinations(near[:12],4):
    u=prod(ps); phiu=prod(p-1 for p in ps)
    for m in range(2,9):
        S=prod(geom(p,m) for p in ps)
        d=gcd(u,S)
        A=u**m-phiu*S
        q=threshold(A,u,m)
        if d==1 and q<ps[0]:
            failure_examples.append((ps,m,q))
            break
    if len(failure_examples)>=12: break
assert proper_examples
assert len(failure_examples)>=12

index_pairs=0
for K in range(4,10):
    L=factorial(K-2)
    for M in range(2,30):
        c=(K-2).bit_length()
        J=L*((max(2,M*(M+c))+L-1)//L)
        for a in range(1,M+1):
            ms=[a*i*J+1 for i in range(1,K-2)]
            for x,y in combinations(ms,2):
                assert gcd(x,y)==1
                index_pairs+=1

print("PASS")
print("exact first-prime statistic cases:",statistic_cases)
print("gap-certified prime recoveries:",gap_recoveries)
print("peeled quotient-query identities:",quotient_identities)
print("proper-gcd scan cases:",gcd_scan_cases)
print("proper-gcd split hits:",proper_gcd_splits)
print("simultaneous-failure examples:",len(failure_examples))
print("aligned effective-index pairs:",index_pairs)
print("first proper-gcd examples:",proper_examples[:3])
print("first failure examples:",failure_examples[:3])
