#!/usr/bin/env python3
from itertools import combinations
from math import gcd, log, ceil

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
            d[p]=d.get(p,0)+1
            n//=p
        p += 1 if p==2 else 2
    if n>1: d[n]=d.get(n,0)+1
    return d

def lcm(a,b):
    return a//gcd(a,b)*b

def support_lambda(fac):
    S=set()
    lam=1
    for p,a in fac.items():
        local=(p-1)*p**(a-1)
        if p==2 and a>=3:
            local=2**(a-2)
        lam=lcm(lam,local)
        S.update(factorint(local))
    return S,lam

def exponent_multiple(N,S):
    E=1
    for r in sorted(S):
        if r>N: continue
        x=r
        while x*r<=N:
            x*=r
        E*=x
    return E

def valuation(n,r):
    a=0
    while n%r==0:
        a+=1; n//=r
    return a

def order_mod(u,p):
    assert gcd(u,p)==1
    o=p-1
    for r in factorint(o):
        while o%r==0 and pow(u,o//r,p)==1:
            o//=r
    return o

def chain_separates(p,q,u,E,S):
    if (u%p==0)!=(u%q==0):
        return True
    if u%p==0 or u%q==0:
        return False
    for r in S:
        er=valuation(E,r)
        rr=1
        for j in range(er+1):
            e=E//rr
            if (pow(u,e,p)==1)!=(pow(u,e,q)==1):
                return True
            rr*=r
    return False

def witness_for_pair(p,q,E,S):
    g=gcd(p-1,q-1)
    A=(p-1)//g; B=(q-1)//g
    assert gcd(A,B)==1 and (A>1 or B>1)
    side=p if A>1 else q
    h=g
    bound=max(3,ceil(2*log(side)**2))
    for u in range(2,bound+1):
        if u%side and pow(u,h,side)!=1:
            assert chain_separates(p,q,u,E,S)
            return u
    # Small moduli are direct finite cases in the proof.
    for u in range(2,side):
        if pow(u,h,side)!=1:
            assert chain_separates(p,q,u,E,S)
            return u
    raise AssertionError((p,q,side,h,bound))

def full_refinement(ps,E,S,witnesses):
    blocks=[tuple(ps)]
    chain=[]
    for r in sorted(S):
        rr=1
        for j in range(valuation(E,r)+1):
            chain.append(E//rr)
            rr*=r
    for u in sorted(set(witnesses)):
        new=[]
        for block in blocks:
            buckets={}
            for p in block:
                if u%p==0:
                    sig=("sat",)
                else:
                    sig=tuple(pow(u,e,p)==1 for e in chain)
                buckets.setdefault(sig,[]).append(p)
            new.extend(tuple(v) for v in buckets.values())
        blocks=new
    assert sorted(len(b) for b in blocks)==[1]*len(ps)

base_primes=primes_upto(31)
cases=[]
for k in (2,3,4):
    cases.extend(combinations(base_primes,k))
extra=[(37,41),(37,43),(41,43),(37,41,43),(31,37,43),
       (29,41,43),(23,37,41,43),(19,31,37,43),(17,29,41,43),(13,31,41,43)]
cases.extend(extra)

counts={"inputs":0,"support":0,"pairs":0,"chains":0,"refine":0,"false":0,"repeat":0}
false_pool=[47,53,59,61,67]
for idx,ps in enumerate(cases):
    N=1
    for p in ps: N*=p
    fac={p:1 for p in ps}
    S,lam=support_lambda(fac)
    fp=false_pool[idx%len(false_pool)]
    if fp not in S and fp not in ps:
        S.add(fp)
    else:
        S.add(71)
    E=exponent_multiple(N,S)
    assert E%lam==0
    counts["inputs"]+=1; counts["support"]+=1; counts["false"]+=1
    witnesses=[]
    for p,q in combinations(ps,2):
        witnesses.append(witness_for_pair(p,q,E,S))
        counts["pairs"]+=1; counts["chains"]+=1
    full_refinement(ps,E,S,witnesses)
    counts["refine"]+=1

P=primes_upto(43)[1:]
for i in range(160):
    p=P[i%len(P)]
    q=P[(3*i+5)%len(P)]
    if q==p: q=P[(3*i+6)%len(P)]
    a=2+i%3
    b=1+(i//3)%3
    fac={p:a,q:b}
    N=p**a*q**b
    S,lam=support_lambda(fac)
    S.add(47 if 47 not in S else 53)
    E=exponent_multiple(N,S)
    assert E%lam==0
    R=N
    for r in S:
        while R%r==0:
            R//=r
    assert all(e==1 for e in factorint(R).values())
    counts["repeat"]+=1

print(f"finite squarefree inputs: {counts['inputs']}")
print(f"support exponent checks: {counts['support']}")
print(f"pair subgroup witnesses: {counts['pairs']}")
print(f"order-chain separators: {counts['chains']}")
print(f"complete refinement checks: {counts['refine']}")
print(f"false-positive support cases: {counts['false']}")
print(f"repeated-prime strip checks: {counts['repeat']}")
print("PASS")
