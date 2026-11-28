#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt, log

def primes_upto(n):
    if n<2:return []
    a=bytearray(b"\x01")*(n+1);a[:2]=b"\x00\x00"
    for p in range(2,isqrt(n)+1):
        if a[p]:a[p*p:n+1:p]=b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(2,n+1) if a[i]]

def factor_primes(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out

def vr(n,r):
    s=0
    while n%r==0:n//=r;s+=1
    return s

def psi(x,y):
    ps=primes_upto(y)
    def smooth(n):
        for p in ps:
            while n%p==0:n//=p
        return n==1
    return sum(smooth(n) for n in range(1,x+1))

def smooth_witness(p,q):
    g=gcd(p-1,q-1);opts=[]
    for high,low in ((p,q),(q,p)):
        x=high-1
        if x==g:continue
        for B in range(2,high):
            if psi(x,B)>g:
                witness=None
                for ell in primes_upto(B):
                    if pow(ell,g,high)!=1:
                        witness=ell;break
                assert witness is not None
                opts.append((B,witness,high,low,g,x//g))
                break
    assert opts
    return min(opts)

def refine_one(D,E,rs,a):
    U=gcd(D,pow(a,D.bit_length(),D))
    initial=[D] if U in (1,D) else [U,D//U]
    out=[]
    for X in initial:
        if gcd(a,X)!=1:
            out.append(X);continue
        parts=[X]
        for r in rs:
            S=vr(E,r)
            for j in range(S+1):
                raw=gcd(pow(a,E//r**j,X)-1,X)
                cut=gcd(X,pow(raw,X.bit_length(),X))
                nxt=[]
                for Y in parts:
                    h=gcd(Y,cut)
                    nxt.extend([h,Y//h] if 1<h<Y else [Y])
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

P=[p for p in primes_upto(65) if p>2]
supports=multiples=pairs=refinements=0
delta_quarter=delta_half=smooth_strict=0
for k in range(2,6):
    for ps in combinations(P,k):
        N=1;lam=1
        for p in ps:N*=p;lam=lcm(lam,p-1)
        if N>2_000_000:continue
        supports+=1
        for mul in range(1,5):
            E=lam*mul;rs=factor_primes(E)
            rem=[p for p in ps if E%p]
            if len(rem)<2:continue
            multiples+=1;ws=[]
            for p,q in combinations(rem,2):
                B,w,h,l,g,m=smooth_witness(p,q)
                assert B<=g+1
                assert w<=B
                assert pow(w,g,h)!=1
                ws.append(w);pairs+=1
                if B<g+1:smooth_strict+=1
                delta=log(m)/log(h-1)
                if delta>=0.25-1e-12:delta_quarter+=1
                if delta>=0.5-1e-12:delta_half+=1
            M=1
            for p in rem:M*=p
            assert full_refine(M,E,rs,max(ws))==rem
            refinements+=1

power_cases=power_refinements=block_checks=0
small=[p for p in primes_upto(31) if p>2]
for k in range(2,5):
    for ps in combinations(small,k):
        for exps in product(range(1,4),repeat=k):
            N=1;lam=1
            for p,a in zip(ps,exps):
                N*=p**a;lam=lcm(lam,p**(a-1)*(p-1))
            if N>3_000_000:continue
            for mul in (1,2,3):
                E=lam*mul;rs=factor_primes(E);rem=[]
                for p,a in zip(ps,exps):
                    if E%p:assert a==1;rem.append(p)
                power_cases+=1
                if len(rem)>=2:
                    ws=[smooth_witness(p,q)[1]
                        for p,q in combinations(rem,2)]
                    M=1
                    for p in rem:M*=p
                    B=max(ws)
                    assert full_refine(M,E,rs,B)==rem
                    for a in range(2,B+1):
                        parts=refine_one(M,E,rs,a)
                        assert all(gcd(x,M//x)==1 for x in parts)
                        block_checks+=len(parts)
                    power_refinements+=1

print(f"squarefree supports: {supports}")
print(f"nontrivial exponent multiples: {multiples}")
print(f"smooth-kernel pair checks: {pairs}")
print(f"strict improvements over g+1 count: {smooth_strict}")
print(f"pairs with delta at least 1/4: {delta_quarter}")
print(f"pairs with delta at least 1/2: {delta_half}")
print(f"complete residual refinements: {refinements}")
print(f"prime-power multiple cases: {power_cases}")
print(f"prime-power residual refinements: {power_refinements}")
print(f"complete-block checks: {block_checks}")
print("PASS")
