#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt

def primes_upto(n):
    a=bytearray(b"\x01")*(n+1); a[:2]=b"\x00\x00"
    for p in range(2,isqrt(n)+1):
        if a[p]: a[p*p:n+1:p]=b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(3,n+1) if a[i]]

def factor_primes(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: out.append(n)
    return out

def vr(n,r):
    s=0
    while n%r==0: n//=r; s+=1
    return s

def order_mod(a,p):
    o=p-1
    for r in factor_primes(p-1):
        while o%r==0 and pow(a,o//r,p)==1: o//=r
    return o

def kernel_witness(p,q,rs):
    g=gcd(p-1,q-1)
    opts=[]
    for high,low in ((p,q),(q,p)):
        m=(high-1)//g
        if m==1: continue
        assert g*m==high-1
        for a in range(2,g+2):
            if pow(a,g,high)!=1:
                assert a<high
                if a%low:
                    oh,ol=order_mod(a,high),order_mod(a,low)
                    good=False
                    for r in rs:
                        if vr(high-1,r)>vr(low-1,r):
                            if vr(oh,r)>vr(ol,r): good=True
                    assert good
                opts.append((a,high,low,m,g))
                break
        else: raise AssertionError
    assert opts
    return min(opts)

def refine_one(D,E,rs,a):
    U=gcd(D,pow(a,D.bit_length(),D))
    initial=[D] if U in (1,D) else [U,D//U]
    out=[]
    for X in initial:
        if gcd(a,X)!=1:
            out.append(X); continue
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
        for D in blocks: nxt.extend(refine_one(D,E,rs,a))
        blocks=sorted(nxt)
    return blocks

P=primes_upto(80)
supports=0; multiples=0; pairs=0; refinements=0
kernel_checks=0; strict_second=0
for k in range(2,6):
    for ps in combinations(P,k):
        N=1; lam=1
        for p in ps: N*=p; lam=lcm(lam,p-1)
        if N>3_000_000: continue
        supports+=1
        for mul in range(1,7):
            E=lam*mul
            rs=factor_primes(E)
            rem=[p for p in ps if E%p]
            if len(rem)<2: continue
            multiples+=1
            witnesses=[]
            G=0
            for p,q in combinations(rem,2):
                w=kernel_witness(p,q,rs)
                witnesses.append(w[0])
                g=gcd(p-1,q-1)
                assert w[0]<=g+1<=min(p,q)
                G=max(G,g+1)
                if g+1<min(p,q): strict_second+=1
                pairs+=1; kernel_checks+=1
            M=1
            for p in rem: M*=p
            B=max(witnesses)
            assert B<=G
            assert full_refine(M,E,rs,B)==rem
            refinements+=1

power_cases=0; power_refinements=0; block_checks=0
small=primes_upto(35)
for k in range(2,5):
    for ps in combinations(small,k):
        for exps in product(range(1,4),repeat=k):
            N=1; lam=1
            for p,a in zip(ps,exps):
                N*=p**a; lam=lcm(lam,p**(a-1)*(p-1))
            if N>5_000_000: continue
            for mul in (1,2,3,5):
                E=lam*mul; rs=factor_primes(E)
                rem=[]
                for p,a in zip(ps,exps):
                    if E%p: assert a==1; rem.append(p)
                power_cases+=1
                if len(rem)>=2:
                    B=max(kernel_witness(p,q,rs)[0]
                          for p,q in combinations(rem,2))
                    M=1
                    for p in rem: M*=p
                    got=full_refine(M,E,rs,B)
                    assert got==rem
                    for a in range(2,B+1):
                        parts=refine_one(M,E,rs,a)
                        assert all(gcd(x,M//x)==1 for x in parts)
                        block_checks+=len(parts)
                    power_refinements+=1

print(f"squarefree supports: {supports}")
print(f"nontrivial exponent multiples: {multiples}")
print(f"kernel-size pair checks: {kernel_checks}")
print(f"strict gcd improvements over smaller-prime bound: {strict_second}")
print(f"complete residual refinements: {refinements}")
print(f"prime-power multiple cases: {power_cases}")
print(f"prime-power residual refinements: {power_refinements}")
print(f"complete-block checks: {block_checks}")
print("PASS")
