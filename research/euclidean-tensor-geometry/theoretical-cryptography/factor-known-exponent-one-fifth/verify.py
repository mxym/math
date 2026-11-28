#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, lcm, isqrt, e, sqrt

def primes_upto(n):
    a=bytearray(b"\x01")*(n+1); a[:2]=b"\x00\x00"
    for p in range(2,isqrt(n)+1):
        if a[p]: a[p*p:n+1:p]=b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(2,n+1) if a[i]]

def factor(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            s=0
            while n%d==0: n//=d; s+=1
            out.append((d,s))
        d+=1
    if n>1: out.append((n,1))
    return out

def vr(n,r):
    s=0
    while n%r==0: n//=r; s+=1
    return s

def signature(p,rs):
    return tuple(vr(p-1,r) for r in rs)

def order_mod(a,p):
    x=p-1
    for r,_ in factor(p-1):
        while x%r==0 and pow(a,x//r,p)==1: x//=r
    return x

def pair_witness(p,q,rs):
    sp,sq=signature(p,rs),signature(q,rs)
    for r,x,y in zip(rs,sp,sq):
        if x==y: continue
        high,low=(p,q) if x>y else (q,p)
        d=abs(x-y)
        for a in range(2,high):
            if pow(a,(high-1)//r**d,high)!=1:
                if a%low:
                    assert vr(order_mod(a,high),r)>vr(order_mod(a,low),r)
                return a
        raise AssertionError
    raise AssertionError

def refine(D,E,rs,B):
    blocks=[D]
    for a in range(2,B+1):
        new=[]
        for X in blocks:
            U=gcd(X,pow(a,X.bit_length(),X))
            parts=[X] if U in (1,X) else [U,X//U]
            for r in rs:
                S=vr(E,r)
                for j in range(S+1):
                    nxt=[]
                    for Y in parts:
                        raw=gcd(pow(a,E//r**j,Y)-1,Y)
                        g=gcd(Y,pow(raw,Y.bit_length(),Y))
                        nxt.extend([g,Y//g] if 1<g<Y else [Y])
                    parts=nxt
            new.extend(parts)
        blocks=sorted(new)
    return blocks

P=[p for p in primes_upto(43) if p>2]
cases=0; advice_branch=0; direct_branch=0
residual_pairs=0; refinements=0; extra_strips=0
for k in range(1,5):
    for ps in combinations(P,k):
        for exps in product(range(1,4),repeat=k):
            N=1; lam=1
            for p,a in zip(ps,exps):
                N*=p**a
                lam=lcm(lam,p**(a-1)*(p-1))
            if N>2_000_000: continue
            for m in range(1,13):
                E=m*lam
                if E%2: E*=2
                fs=factor(E); rs=[r for r,_ in fs]
                assert E==__import__("math").prod(r**s for r,s in fs)
                rem=[]; M=1
                for p,a in zip(ps,exps):
                    if E%p==0:
                        extra_strips+=1
                    else:
                        assert a==1
                        rem.append(p); M*=p
                assert len(set(signature(p,rs) for p in rem))==len(rem)
                cases+=1
                if E<N: advice_branch+=1
                else: direct_branch+=1
                if len(rem)>=2:
                    B=max(pair_witness(p,q,rs)
                          for p,q in combinations(rem,2))
                    assert refine(M,E,rs,B)==rem
                    residual_pairs+=len(list(combinations(rem,2)))
                    refinements+=1

theta=1/(4*sqrt(e))
assert theta < 1/5
print(f"factored-multiple cases: {cases}")
print(f"E < N branch cases: {advice_branch}")
print(f"N <= E branch cases: {direct_branch}")
print(f"stripped prime-power entries: {extra_strips}")
print(f"residual pair checks: {residual_pairs}")
print(f"complete residual refinements: {refinements}")
print(f"character exponent: {theta:.12f}")
print("PASS")
