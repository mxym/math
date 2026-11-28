#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, isqrt

def primes_upto(n):
    a=bytearray(b"\x01")*(n+1)
    a[:2]=b"\x00\x00"
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(2,n+1) if a[i]]

def is_prime(n):
    if n<2:return False
    for d in range(2,isqrt(n)+1):
        if n%d==0:return False
    return True

def prime_factors(n):
    out=[];d=2
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

def support_exponent(N,S):
    E=1
    for r in S:
        if r>N:continue
        u=1
        while u<=N//r:u*=r
        E*=u
    return E

def is_smooth(n,y):
    if n==1:return True
    d=2
    while d*d<=n:
        while n%d==0:
            if d>y:return False
            n//=d
        d+=1
    return n==1 or n<=y

def psi(x,y):
    return sum(is_smooth(n,y) for n in range(1,x+1))

def refine_one(D,E,S,a):
    U=gcd(D,pow(a,D.bit_length(),D))
    initial=[D] if U in (1,D) else [U,D//U]
    out=[]
    for X in initial:
        if gcd(a,X)!=1:
            out.append(X);continue
        parts=[X]
        for r in S:
            t=vr(E,r)
            for j in range(t+1):
                raw=gcd(pow(a,E//(r**j),X)-1,X)
                cut=gcd(X,pow(raw,X.bit_length(),X))
                nxt=[]
                for Y in parts:
                    h=gcd(Y,cut)
                    nxt.extend([h,Y//h] if 1<h<Y else [Y])
                parts=nxt
        out.extend(parts)
    return sorted(out)

def refine_bases(N,E,S,y):
    blocks=[N]
    for a in range(2,y+1):
        nxt=[]
        for D in blocks:nxt.extend(refine_one(D,E,S,a))
        blocks=sorted(nxt)
    return blocks

def reduced_bound(ps):
    T=1
    for p,q in combinations(ps,2):
        g=gcd(p-1,q-1)
        T=max(T,(p-1)//g,(q-1)//g)
    return T

def monotone_root(D,ratios):
    den=1
    for a,b in ratios:den*=b
    target=D*den
    lo,hi=1,D
    while lo<=hi:
        x=(lo+hi)//2
        val=x+1
        for a,b in ratios:val*=a*x+b
        if val<target:lo=x+1
        elif val>target:hi=x-1
        else:return x
    return None

def recover_block(D,K,T):
    candidates=[(a,b) for a in range(1,T+1)
                for b in range(1,T+1) if gcd(a,b)==1]
    tested=0
    for t in range(2,K+1):
        for ratios in product(candidates,repeat=t-1):
            tested+=1
            x=monotone_root(D,ratios)
            if x is None:continue
            ps=[x+1]
            ok=True
            for a,b in ratios:
                if (a*x)%b:
                    ok=False;break
                ps.append((a*x)//b+1)
            if ok and len(set(ps))==len(ps) and all(is_prime(p) for p in ps):
                z=1
                for p in ps:z*=p
                if z==D:return sorted(ps),tested
    return None,tested

P=[p for p in primes_upto(31) if p>2]
Y=2
inputs=0
support_checks=0
base_blocks=0
pair_obstruction_checks=0
recovered_blocks=0
ratio_tuples_tested=0
four_factor_checks=0
power_strip_checks=0

for k in (2,3):
    for ps in combinations(P,k):
        N=1;lam=1
        for p in ps:
            N*=p
            lam=lam*(p-1)//gcd(lam,p-1)
        S=prime_factors(lam)
        E=support_exponent(N,S)
        assert E%lam==0
        support_checks+=1
        blocks=refine_bases(N,E,S,Y)
        assert all(gcd(D,N//D)==1 for D in blocks)
        base_blocks+=len(blocks)
        for D in blocks:
            qs=[p for p in ps if D%p==0]
            if len(qs)==1:
                assert D==qs[0];continue
            for p,q in combinations(qs,2):
                g=gcd(p-1,q-1)
                assert psi(p-1,min(Y,p-1))<=g
                assert psi(q-1,min(Y,q-1))<=g
                pair_obstruction_checks+=1
            T=reduced_bound(qs)
            got,tested=recover_block(D,k,T)
            assert got==sorted(qs)
            recovered_blocks+=1
            ratio_tuples_tested+=tested
        Tall=reduced_bound(ps)
        got_all,tested_all=recover_block(N,k,Tall)
        assert got_all==sorted(ps)
        recovered_blocks+=1
        ratio_tuples_tested+=tested_all
        inputs+=1

unseparated=[
    (23,89),
    (53,157,1613),
]
for ps in unseparated:
    N=1;lam=1
    for p in ps:
        N*=p;lam=lam*(p-1)//gcd(lam,p-1)
    S=prime_factors(lam);E=support_exponent(N,S)
    blocks=refine_bases(N,E,S,Y)
    assert blocks==[N]
    for p,q in combinations(ps,2):
        g=gcd(p-1,q-1)
        assert psi(p-1,min(Y,p-1))<=g
        assert psi(q-1,min(Y,q-1))<=g
        pair_obstruction_checks+=1
    T=reduced_bound(ps)
    got,tested=recover_block(N,len(ps),T)
    assert got==sorted(ps)
    recovered_blocks+=1
    ratio_tuples_tested+=tested

curated=[
    (5,7,13,17),
    (7,13,19,31),
    (5,11,17,31),
]
for ps in curated:
    N=1;lam=1
    for p in ps:
        N*=p;lam=lam*(p-1)//gcd(lam,p-1)
    S=prime_factors(lam);E=support_exponent(N,S)
    blocks=refine_bases(N,E,S,Y)
    for D in blocks:
        qs=[p for p in ps if D%p==0]
        if len(qs)>=2:
            T=reduced_bound(qs)
            got,tested=recover_block(D,4,T)
            assert got==sorted(qs)
            ratio_tuples_tested+=tested
            recovered_blocks+=1
    four_factor_checks+=1

# Arbitrary multiplicities: every repeated residual prime is listed in the
# support and is removed with its full exponent.
for ps in combinations(P[:6],3):
    for exps in ((2,1,1),(1,3,1),(2,2,2)):
        N=1;lam=1
        for p,e in zip(ps,exps):
            N*=p**e
            term=p**(e-1)*(p-1)
            lam=lam*term//gcd(lam,term)
        S=prime_factors(lam);E=support_exponent(N,S)
        assert E%lam==0
        for p,e in zip(ps,exps):
            if e>=2:
                assert p in S and N%(p**e)==0
                power_strip_checks+=1

print(f"squarefree inputs: {inputs}")
print(f"support exponent checks: {support_checks}")
print(f"post-scan blocks: {base_blocks}")
print(f"unseparated pair obstruction checks: {pair_obstruction_checks}")
print(f"ratio-reconstructed blocks: {recovered_blocks}")
print(f"ratio tuples tested: {ratio_tuples_tested}")
print(f"four-factor curated inputs: {four_factor_checks}")
print(f"repeated-prime strip checks: {power_strip_checks}")
print("PASS")
