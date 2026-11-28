#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, isqrt, factorial

def primes_upto(n):
    a=[True]*(n+1)
    a[0]=a[1]=False
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=[False]*(((n-p*p)//p)+1)
    return [i for i,v in enumerate(a) if v]

PRIMES=primes_upto(80)

def ceil_log2(n):
    return (n-1).bit_length()

def value(fac):
    z=1
    for p,a in fac:
        z*=p**a
    return z

def phi_fac(fac):
    z=1
    for p,a in fac:
        z*=p**(a-1)*(p-1)
    return z

def geom(p,m):
    return (p**m-1)//(p-1)

def sigma_power(fac,J):
    z=1
    for p,a in fac:
        z*=geom(p,a*J+1)
    return z

def compositions(n,k):
    if k==1:
        yield (n,)
    else:
        for a in range(1,n-k+2):
            for tail in compositions(n-a,k-1):
                yield (a,)+tail

index_cases=0
for K in range(3,10):
    r=K-2
    L=factorial(r)
    for M in range(2,41):
        J=L*((max(2,M)+L-1)//L)
        for a in range(1,M+1):
            ms=[a*i*J+1 for i in range(1,r+1)]
            for x,y in combinations(ms,2):
                assert gcd(x,y)==1
            index_cases+=1

floor_cases=0
grouping_cases=0
for k in range(1,7):
    for ps in combinations(PRIMES[:7],k):
        for exps in product(range(1,3),repeat=k):
            fac=list(zip(ps,exps))
            n=value(fac)
            M=ceil_log2(n)
            J=max(2,M)
            assert n**(J+1)//sigma_power(fac,J)==phi_fac(fac)
            floor_cases+=1

            ph=phi_fac(fac)
            R=n//gcd(n,ph)
            assert R>1
            U=gcd(n,R**M)
            V=n//U
            ufac=[(p,a) for p,a in fac if R%p==0]
            vfac=[(p,a) for p,a in fac if R%p!=0]
            assert U==value(ufac) and V==value(vfac)
            assert R==value([(p,1) for p,a in ufac])
            recovered={}
            w={}
            for j in range(1,M+2):
                w[j]=gcd(U,R**j)//gcd(U,R**(j-1))
            for j in range(1,M+1):
                b=w[j]//w[j+1]
                if b>1:
                    recovered[j]=b
            actual={}
            for p,a in ufac:
                actual[a]=actual.get(a,1)*p
            assert recovered==actual
            grouping_cases+=1

budget_cases=0
for K in range(3,10):
    q=K-2
    for k in range(3,K+1):
        # all-equal case
        assert k-3<q
        budget_cases+=1
        for h in range(0,k):
            known=k-h
            if known<1:
                continue
            for g in range(1,known+1):
                for parts in compositions(known,g):
                    if h==0 and g==1:
                        continue
                    if h>=2:
                        cap_inf=sum(x-1 for x in parts)+(h-2)
                        assert cap_inf==k-g-2 and cap_inf<q
                        budget_cases+=1
                    if h>0:
                        cap_known_boundary=sum(x-1 for x in parts)-1+(h-1)
                        assert cap_known_boundary==k-g-2 and cap_known_boundary<q
                        budget_cases+=1
                    elif g>=2:
                        cap_known_boundary=sum(x-1 for x in parts)-1
                        assert cap_known_boundary==k-g-1 and cap_known_boundary<q
                        budget_cases+=1

samples=[
    (5,[(2,1),(3,2),(5,1),(7,3),(11,2)]),
    (5,[(2,2),(3,2),(5,3),(7,3),(11,3)]),
    (6,[(2,1),(3,2),(5,3),(7,1),(11,2),(13,3)]),
    (7,[(2,2),(3,2),(5,2),(7,3),(11,3),(13,1),(17,1)]),
]
query_identity_cases=0
sample_group_cases=0
for K,fac in samples:
    n=value(fac)
    M=ceil_log2(n)
    r=K-2
    L=factorial(r)
    J=L*((max(2,M)+L-1)//L)
    ph=phi_fac(fac)
    R=n//gcd(n,ph)
    U=gcd(n,R**M)
    V=n//U
    known=[(p,a) for p,a in fac if R%p==0]
    unknown=[(p,a) for p,a in fac if R%p!=0]
    groups={}
    for p,a in known:
        groups.setdefault(a,[]).append(p)
    assert U==value(known) and V==value(unknown)
    sample_group_cases+=1
    for i in range(1,r+1):
        Ji=i*J
        left=1
        for a,ps in groups.items():
            block=1
            for p in ps:
                block*=geom(p,a*Ji+1)
            left*=block
        for p,a in unknown:
            left*=geom(p,a*Ji+1)
        assert left==sigma_power(fac,Ji)
        query_identity_cases+=1

print("PASS")
print("pairwise effective-index cases:",index_cases)
print("totient-floor cases:",floor_cases)
print("exact equal-order grouping cases:",grouping_cases)
print("projective boundary-budget cases:",budget_cases)
print("mixed structural samples:",sample_group_cases)
print("true sparse-query identities:",query_identity_cases)
