#!/usr/bin/env python3
from itertools import combinations
from fractions import Fraction
from math import gcd

def primes_upto(n):
    out=[]
    for x in range(2,n+1):
        if all(x%p for p in out if p*p<=x):
            out.append(x)
    return out

def factorint(n):
    d={}
    p=2
    while p*p<=n:
        while n%p==0:
            d[p]=d.get(p,0)+1; n//=p
        p += 1 if p==2 else 2
    if n>1: d[n]=d.get(n,0)+1
    return d

def lcm(a,b): return a//gcd(a,b)*b

def support_lambda(fac):
    S=set(); lam=1
    for p,a in fac.items():
        local=(p-1)*p**(a-1)
        if p==2 and a>=3: local=2**(a-2)
        lam=lcm(lam,local)
        S.update(factorint(local))
    return S,lam

def exponent_multiple(N,S):
    E=1
    for r in S:
        if r>N: continue
        x=r
        while x*r<=N: x*=r
        E*=x
    return E

def v2(n):
    e=0
    while n%2==0:
        e+=1; n//=2
    return e

def order_mod(a,p):
    o=p-1
    for r in factorint(o):
        while o%r==0 and pow(a,o//r,p)==1: o//=r
    return o

def h_law(p):
    if p==2: return {0:Fraction(1)}
    e=v2(p-1)
    d={0:Fraction(1,2**e)}
    for k in range(1,e+1): d[k]=Fraction(2**(k-1),2**e)
    assert sum(d.values())==1 and max(d.values())<=Fraction(1,2)
    return d

def collision_probability(ps):
    laws=[h_law(p) for p in ps]
    keys=set().union(*laws)
    c=sum((__import__("functools").reduce(lambda x,y:x*y,
            (law.get(k,Fraction(0)) for law in laws),Fraction(1)))
          for k in keys)
    assert c<=Fraction(1,2)
    return c

def split_with_power(M,E,a):
    g=gcd(a,M)
    if 1<g<M: return g
    if g!=1: return None
    s=v2(E); t=E>>s
    b=pow(a,t,M)
    if b==1: return None
    for _ in range(s):
        c=b*b%M
        if c==1:
            d=gcd(b-1,M)
            return d if 1<d<M else None
        b=c
    raise AssertionError("annihilating exponent failed")

Ps=primes_upto(31)
cases=[]
for k in (2,3,4): cases.extend(combinations(Ps,k))
extra=[(37,41),(37,43),(41,43),(37,41,43),(31,37,43),
       (29,41,43),(23,37,41,43),(19,31,37,43),(17,29,41,43),(13,31,41,43)]
cases.extend(extra)
counts={"support":0,"profiles":0,"exact":0,"residues":0,"false":0,"repeat":0}
small=[]
for idx,ps in enumerate(cases):
    N=1
    for p in ps:N*=p
    S,lam=support_lambda({p:1 for p in ps})
    fp=[47,53,59,61,67][idx%5]
    S.add(fp if fp not in ps else 71)
    E=exponent_multiple(N,S)
    assert E%lam==0
    counts["support"]+=1; counts["false"]+=1
    collision_probability(ps); counts["profiles"]+=1
    if N<=12000: small.append((ps,N,E))

for ps,M,E in small:
    unit=0; fail=0
    for a in range(M):
        if gcd(a,M)==1:
            unit+=1
            hs=[v2(order_mod(a%p,p)) for p in ps]
            expected_fail=len(set(hs))==1
            got=split_with_power(M,E,a)
            if (got is None)!=expected_fail:
                raise AssertionError((ps,M,E,a,hs,got))
            if got is None: fail+=1
            else: assert M%got==0
    assert Fraction(fail,unit)==collision_probability(ps)
    counts["exact"]+=1; counts["residues"]+=unit

Q=primes_upto(43)
for i in range(160):
    p=Q[1+i%len(Q[1:])]
    q=Q[1+(3*i+5)%len(Q[1:])]
    if p==q:q=Q[1+(3*i+6)%len(Q[1:])]
    fac={p:2+i%3,q:1+(i//4)%3}
    N=1
    for r,a in fac.items():N*=r**a
    S,lam=support_lambda(fac); S.add(47 if 47 not in S else 53)
    E=exponent_multiple(N,S); assert E%lam==0
    R=N
    for r in S:
        while R%r==0:R//=r
    assert all(a==1 for a in factorint(R).values())
    counts["repeat"]+=1

print(f"support exponent cases: {counts['support']}")
print(f"exact CRT probability profiles: {counts['profiles']}")
print(f"exhaustive split blocks: {counts['exact']}")
print(f"exhaustive unit residues: {counts['residues']}")
print(f"false-positive advice cases: {counts['false']}")
print(f"repeated-prime strip checks: {counts['repeat']}")
print("PASS")
