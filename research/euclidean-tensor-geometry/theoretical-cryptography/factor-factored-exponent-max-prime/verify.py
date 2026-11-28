#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt

def primes_upto(n):
    a = bytearray(b"\x01")*(n+1)
    a[:2] = b"\x00\x00"
    for p in range(2, isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p] = b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(3,n+1) if a[i]]

def prime_factors(n):
    out=[]
    d=2
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
        n//=r;t+=1
    return t

def order_mod(a,m,exponent):
    x,fac,d=exponent,[],2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:fac.append(x)
    out=exponent
    for d in fac:
        while out%d==0 and pow(a,out//d,m)==1:out//=d
    return out

def signature(p,rs):
    return tuple(vr(p-1,r) for r in rs)

def pair_witness(p,q,rs):
    sp,sq=signature(p,rs),signature(q,rs)
    assert sp!=sq
    for r,x,y in zip(rs,sp,sq):
        if x==y:continue
        high,low=(p,q) if x>y else (q,p)
        d=abs(x-y)
        for a in range(2,high):
            if pow(a,(high-1)//(r**d),high)!=1:
                return a,high,r
        raise AssertionError
    raise AssertionError

def refine_one(D,E,rs,a):
    L=D.bit_length()
    U=gcd(D,pow(a,L,D))
    initial=[D] if U in (1,D) else [U,D//U]
    out=[]
    for X in initial:
        if gcd(a,X)!=1:
            out.append(X);continue
        parts=[X]
        for r in rs:
            S=vr(E,r)
            for j in range(S+1):
                raw=gcd(pow(a,E//(r**j),X)-1,X)
                cut=gcd(X,pow(raw,X.bit_length(),X))
                nxt=[]
                for Y in parts:
                    g=gcd(Y,cut)
                    nxt.extend([g,Y//g] if 1<g<Y else [Y])
                parts=nxt
        out.extend(parts)
    return out

def full_refine(N,E,rs,B):
    blocks=[N]
    for a in range(2,B+1):
        nxt=[]
        for D in blocks:nxt.extend(refine_one(D,E,rs,a))
        blocks=sorted(nxt)
    return blocks

P=primes_upto(80)
supports=0
residual_supports=0
pair_checks=0
refinements=0
stripped_primes=0
for k in range(2,6):
    for ps in combinations(P,k):
        N=1;E=1
        for p in ps:
            N*=p;E=lcm(E,p-1)
        if N>3_000_000:continue
        supports+=1
        rs=prime_factors(E)
        stripped=[p for p in ps if E%p==0]
        rem=[p for p in ps if E%p]
        stripped_primes+=len(stripped)
        assert len({signature(p,rs) for p in rem})==len(rem)
        if len(rem)<2:continue
        residual_supports+=1
        B=2
        for p,q in combinations(rem,2):
            a,Q,r=pair_witness(p,q,rs)
            assert a<Q<=max(rem)
            x,y=vr(p-1,r),vr(q-1,r)
            high,low=(p,q) if x>y else (q,p)
            assert pow(a,(high-1)//(r**abs(x-y)),high)!=1
            if a%low:
                assert vr(order_mod(a,high,high-1),r)>\
                       vr(order_mod(a,low,low-1),r)
            B=max(B,a);pair_checks+=1
        M=1
        for p in rem:M*=p
        assert full_refine(M,E,rs,B)==rem
        refinements+=1

power_cases=0
power_residuals=0
block_checks=0
smallP=primes_upto(35)
for k in range(2,5):
    for ps in combinations(smallP,k):
        for exps in product(range(1,4),repeat=k):
            N=1;E=1;known=[];rem=[]
            for p,e in zip(ps,exps):
                pe=p**e;N*=pe
                E=lcm(E,p**(e-1)*(p-1))
            if N>5_000_000:continue
            power_cases+=1
            rs=prime_factors(E)
            for p,e in zip(ps,exps):
                if E%p==0:known.append(p**e)
                else:
                    assert e==1
                    rem.append(p)
            assert len({signature(p,rs) for p in rem})==len(rem)
            if len(rem)>=2:
                B=max(pair_witness(p,q,rs)[0]
                      for p,q in combinations(rem,2))
                M=1
                for p in rem:M*=p
                got=full_refine(M,E,rs,B)
                assert got==rem
                for a in range(2,min(B,25)+1):
                    parts=refine_one(M,E,rs,a)
                    assert all(gcd(x,M//x)==1 for x in parts)
                    block_checks+=len(parts)
                power_residuals+=1

print(f"squarefree supports: {supports}")
print(f"residual supports with at least two primes: {residual_supports}")
print(f"prime-conductor pair checks: {pair_checks}")
print(f"complete residual refinements: {refinements}")
print(f"small prime factors stripped: {stripped_primes}")
print(f"prime-power inputs: {power_cases}")
print(f"nontrivial prime-power residuals: {power_residuals}")
print(f"complete-block checks: {block_checks}")
print("PASS")
