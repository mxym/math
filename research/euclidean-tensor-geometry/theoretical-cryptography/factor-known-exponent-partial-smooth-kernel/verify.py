#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt, log, ceil

Y=7
R=[2,3,5,7]
DELTA=0.25
A=5.0

def primes_upto(n):
    if n<2:return []
    a=bytearray(b"\x01")*(n+1);a[:2]=b"\x00\x00"
    for p in range(2,isqrt(n)+1):
        if a[p]:a[p*p:n+1:p]=b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(2,n+1) if a[i]]

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

def orientation(p,q):
    opts=[]
    for high,low in ((p,q),(q,p)):
        m=1
        for r in R:
            m*=r**max(0,vr(high-1,r)-vr(low-1,r))
        if m==1:continue
        assert (high-1)%m==0
        k=(high-1)//m
        delta=log(m)/log(high-1)
        for B in range(2,high):
            if psi(high-1,B)>k:
                w=None
                for ell in primes_upto(B):
                    if pow(ell,k,high)!=1:
                        w=ell;break
                assert w is not None
                opts.append((delta,B,w,high,low,m,k))
                break
    return opts

def refine_one(D,E,a):
    U=gcd(D,pow(a,D.bit_length(),D))
    initial=[D] if U in (1,D) else [U,D//U]
    out=[]
    for X in initial:
        if gcd(a,X)!=1:
            out.append(X);continue
        parts=[X]
        for r in R:
            S=vr(E,r)
            for j in range(S+1):
                raw=gcd(pow(a,E//r**j,X)-1,X)
                cut=gcd(X,pow(raw,X.bit_length(),X))
                nxt=[]
                for Z in parts:
                    h=gcd(Z,cut)
                    nxt.extend([h,Z//h] if 1<h<Z else [Z])
                parts=nxt
        out.extend(parts)
    return out

def full_refine(N,E,B):
    blocks=[N]
    for a in range(2,B+1):
        nxt=[]
        for D in blocks:nxt.extend(refine_one(D,E,a))
        blocks=sorted(nxt)
    return blocks

P=[p for p in primes_upto(79) if p>Y]
supports=qualified=excluded=pairs=refinements=0
smooth_checks=block_checks=0
for k in range(2,6):
    for ps in combinations(P,k):
        N=1;lam=1
        for p in ps:N*=p;lam=lcm(lam,p-1)
        if N>3_000_000:continue
        supports+=1
        for mul in range(1,5):
            E=lam*mul
            chosen=[];ok=True
            for p,q in combinations(ps,2):
                opts=orientation(p,q)
                good=[o for o in opts if o[0]>=DELTA-1e-12]
                if not good:ok=False;break
                best=min(good,key=lambda o:(o[1],o[2]))
                delta,B,w,h,l,m,ker=best
                assert psi(h-1,B)>ker
                assert pow(w,ker,h)!=1
                chosen.append(w);pairs+=1;smooth_checks+=1
            if not ok:
                excluded+=1;continue
            qualified+=1
            budget=ceil(log(N)**A)
            assert max(chosen)<=budget
            assert full_refine(N,E,max(chosen))==list(ps)
            refinements+=1

power_cases=power_qualified=power_refinements=0
small=[p for p in primes_upto(43) if p>Y]
for k in range(2,5):
    for ps in combinations(small,k):
        for exps in product(range(1,4),repeat=k):
            N=1;lam=1
            for p,a in zip(ps,exps):
                N*=p**a;lam=lcm(lam,p**(a-1)*(p-1))
            if N>4_000_000:continue
            E=lam
            power_cases+=1;chosen=[];ok=True
            for p,q in combinations(ps,2):
                good=[o for o in orientation(p,q)
                      if o[0]>=DELTA-1e-12]
                if not good:ok=False;break
                chosen.append(min(good,key=lambda o:(o[1],o[2]))[2])
            if not ok:continue
            power_qualified+=1
            B=max(chosen)
            target=sorted(p**a for p,a in zip(ps,exps))
            assert full_refine(N,E,B)==target
            for a in range(2,B+1):
                parts=refine_one(N,E,a)
                assert all(gcd(x,N//x)==1 for x in parts)
                block_checks+=len(parts)
            power_refinements+=1

print(f"small signature primes: {R}")
print(f"squarefree supports: {supports}")
print(f"qualified exponent multiples: {qualified}")
print(f"excluded exponent multiples: {excluded}")
print(f"qualified pair checks: {pairs}")
print(f"smooth-kernel checks: {smooth_checks}")
print(f"complete residual refinements: {refinements}")
print(f"prime-power cases: {power_cases}")
print(f"qualified prime-power cases: {power_qualified}")
print(f"prime-power refinements: {power_refinements}")
print(f"complete-block checks: {block_checks}")
print("PASS")
