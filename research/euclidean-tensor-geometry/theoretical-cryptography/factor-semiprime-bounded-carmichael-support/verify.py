#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, isqrt

def primes_upto(n):
    out=[]
    for x in range(2,n+1):
        if all(x%p for p in out if p*p<=x): out.append(x)
    return out

def factorint(n):
    d={}; p=2
    while p*p<=n:
        while n%p==0:d[p]=d.get(p,0)+1;n//=p
        p += 1 if p==2 else 2
    if n>1:d[n]=d.get(n,0)+1
    return d

def lcm(a,b):return a//gcd(a,b)*b

def lam_semiprime(p,q):return lcm(p-1,q-1)

def exponent_ranges(N,S):
    out=[]
    for r in sorted(x for x in S if x<=N):
        e=0;x=1
        while x*r<=N:e+=1;x*=r
        out.append((r,e))
    return out

def verify_factor(N,d):
    if not (1<d<N and N%d==0):return None
    e=N//d
    if all(d%p for p in range(2,isqrt(d)+1)) and all(e%p for p in range(2,isqrt(e)+1)):
        return tuple(sorted((d,e)))
    return None

def recover(N,S):
    rs=exponent_ranges(N,S)
    tested=0
    for es in product(*(range(e+1) for _,e in rs)):
        m=1
        for (r,_),e in zip(rs,es):m*=r**e
        tested+=1
        D=N//m
        got=verify_factor(N,D)
        if got:return got,tested
        phi=D*m
        sm=N+1-phi
        disc=sm*sm-4*N
        if disc<0:continue
        z=isqrt(disc)
        if z*z!=disc or (sm+z)%2:continue
        got=verify_factor(N,(sm+z)//2)
        if got:return got,tested
    return None,tested

P=primes_upto(61)
pairs=list(combinations(P,2))
counts={"pairs":0,"candidates":0,"first":0,"quad":0,"false":0,"square":0}
for idx,(p,q) in enumerate(pairs):
    N=p*q
    lam=lam_semiprime(p,q)
    S=set(factorint(lam))
    fp=[37,41,43,47,53,59][idx%6]
    if fp in S:S.add(67)
    else:S.add(fp)
    got,tested=recover(N,S)
    assert got==(p,q)
    counts["pairs"]+=1;counts["candidates"]+=tested;counts["false"]+=1
    D=N//lam
    if verify_factor(N,D):counts["first"]+=1
    else:
        phi=D*lam;sm=N+1-phi;z=isqrt(sm*sm-4*N)
        assert tuple(sorted(((sm-z)//2,(sm+z)//2)))==(p,q)
        counts["quad"]+=1

for p in P:
    N=p*p
    z=isqrt(N)
    assert z*z==N and z==p
    counts["square"]+=1

print(f"semiprime support cases: {counts['pairs']}")
print(f"support candidates tested: {counts['candidates']}")
print(f"floor-factor branch: {counts['first']}")
print(f"quadratic branch: {counts['quad']}")
print(f"false-positive support cases: {counts['false']}")
print(f"square direct cases: {counts['square']}")
print("PASS")
