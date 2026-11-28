#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt

def primes_upto(n):
    a=bytearray(b"\x01")*(n+1)
    a[:2]=b"\x00\x00"
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(2,n+1) if a[i]]

def prime_factors(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out

def vr(n,r):
    t=0
    while n%r==0:
        n//=r; t+=1
    return t

def pp_lambda(p,e):
    if p==2:
        return 1 if e==1 else (2 if e==2 else 2**(e-2))
    return p**(e-1)*(p-1)

def support_exponent(N,S):
    E=1
    for r in sorted(set(S)):
        if r>N:continue
        u=1
        while u<=N//r:u*=r
        E*=u
    return E

def signature(p,S):
    return tuple(vr(p-1,r) for r in S)

def pair_witness(p,q,S):
    sp,sq=signature(p,S),signature(q,S)
    assert sp!=sq
    for r,x,y in zip(S,sp,sq):
        if x==y:continue
        high,low=(p,q) if x>y else (q,p)
        d=abs(x-y)
        for a in range(2,high):
            if pow(a,(high-1)//(r**d),high)!=1:
                return a,high,r
        raise AssertionError
    raise AssertionError

def refine_one(D,E,S,a):
    L=D.bit_length()
    U=gcd(D,pow(a,L,D))
    initial=[D] if U in (1,D) else [U,D//U]
    out=[]
    for X in initial:
        if gcd(a,X)!=1:
            out.append(X); continue
        parts=[X]
        for r in S:
            T=vr(E,r)
            for j in range(T+1):
                raw=gcd(pow(a,E//(r**j),X)-1,X)
                cut=gcd(X,pow(raw,X.bit_length(),X))
                nxt=[]
                for Y in parts:
                    g=gcd(Y,cut)
                    nxt.extend([g,Y//g] if 1<g<Y else [Y])
                parts=nxt
        out.extend(parts)
    return out

def full_refine(N,E,S,B):
    blocks=[N]
    for a in range(2,B+1):
        nxt=[]
        for D in blocks:nxt.extend(refine_one(D,E,S,a))
        blocks=sorted(nxt)
    return blocks

P=primes_upto(67)
extras=[43,47]
supports=0
superset_cases=0
pair_checks=0
refinements=0
lambda_divisibility=0
stripped=0
for k in range(2,6):
    for ps in combinations(P,k):
        N=1; lam=1
        for p in ps:
            N*=p; lam=lcm(lam,p-1)
        if N>2_500_000:continue
        base=prime_factors(lam)
        variants=[base,sorted(set(base+[r for r in extras if r<=N]))]
        for S in variants:
            E=support_exponent(N,S)
            assert E%lam==0
            assert E.bit_length()<=len(S)*N.bit_length()+1
            lambda_divisibility+=1
            known=[p for p in ps if p in S]
            rem=[p for p in ps if p not in S]
            stripped+=len(known)
            assert len({signature(p,S) for p in rem})==len(rem)
            if len(rem)>=2:
                B=2
                for p,q in combinations(rem,2):
                    a,high,r=pair_witness(p,q,S)
                    assert a<high<=max(rem)
                    B=max(B,a); pair_checks+=1
                M=1
                for p in rem:M*=p
                assert full_refine(M,E,S,B)==rem
                refinements+=1
            superset_cases+=1
        supports+=1

power_cases=0
power_refinements=0
block_checks=0
small=primes_upto(29)
for k in range(2,5):
    for ps in combinations(small,k):
        for es in product(range(1,4),repeat=k):
            N=1;lam=1;target=[]
            for p,e in zip(ps,es):
                N*=p**e; lam=lcm(lam,pp_lambda(p,e))
            if N>3_000_000:continue
            S=prime_factors(lam)
            if 31<=N:S=sorted(set(S+[31]))
            E=support_exponent(N,S)
            assert E%lam==0
            power_cases+=1
            rem=[]
            for p,e in zip(ps,es):
                if p not in S:
                    assert e==1
                    rem.append(p)
            assert len({signature(p,S) for p in rem})==len(rem)
            if len(rem)>=2:
                B=max(pair_witness(p,q,S)[0] for p,q in combinations(rem,2))
                M=1
                for p in rem:M*=p
                assert full_refine(M,E,S,B)==rem
                for a in range(2,min(B,19)+1):
                    parts=refine_one(M,E,S,a)
                    assert all(gcd(x,M//x)==1 for x in parts)
                    block_checks+=len(parts)
                power_refinements+=1

print(f"squarefree supports: {supports}")
print(f"support-superset cases: {superset_cases}")
print(f"lambda-divisibility checks: {lambda_divisibility}")
print(f"small primes stripped: {stripped}")
print(f"prime-conductor pair checks: {pair_checks}")
print(f"complete residual refinements: {refinements}")
print(f"prime-power inputs: {power_cases}")
print(f"nontrivial prime-power refinements: {power_refinements}")
print(f"complete-block checks: {block_checks}")
print("PASS")
