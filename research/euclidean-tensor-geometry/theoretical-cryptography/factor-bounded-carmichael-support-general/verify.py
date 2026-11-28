#!/usr/bin/env python3
from itertools import combinations, product
from math import isqrt

def primes_upto(n):
    out=[]
    for x in range(2,n+1):
        if all(x%p for p in out if p*p<=x):out.append(x)
    return out

def isprime(n):
    return n>=2 and all(n%p for p in range(2,isqrt(n)+1))

def factorint(n):
    d={};p=2
    while p*p<=n:
        while n%p==0:d[p]=d.get(p,0)+1;n//=p
        p += 1 if p==2 else 2
    if n>1:d[n]=d.get(n,0)+1
    return d

def support_lambda(fac):
    S=set()
    for p,a in fac.items():
        local=(p-1)*p**(a-1)
        if p==2 and a>=3:local=2**(a-2)
        S.update(factorint(local))
    return S

def exponent_ranges(N,S):
    out=[]
    for r in sorted(x for x in S if x<=N):
        e=0;x=1
        while x*r<=N:e+=1;x*=r
        out.append((r,e))
    return out

def recover(N,S):
    R=N;out={};tested=0
    rs=exponent_ranges(N,S)
    for es in product(*(range(e+1) for _,e in rs)):
        d=1
        for (r,_),e in zip(rs,es):d*=r**e
        tested+=1
        if d>=N:continue
        c=d+1
        if not isprime(c) or R%c:continue
        a=0
        while R%c==0:a+=1;R//=c
        out[c]=a
        if R==1:break
    assert R==1
    return out,tested

P=primes_upto(19)
cases=[]
idx=0
for k in (1,2,3):
    for ps in combinations(P,k):
        exps=tuple(1+(idx+j)%2 for j,_ in enumerate(ps))
        cases.append((ps,exps));idx+=1
extra=[((2,3,5),(4,3,2)),((7,11,13),(2,2,2)),((17,19),(3,2)),
       ((2,19),(5,3)),((3,5,7),(3,2,2))]
cases.extend(extra)
counts={"inputs":0,"vectors":0,"factors":0,"repeat":0,"false":0,"two":0}
fps=[23,29,31,37,41]
for i,(ps,es) in enumerate(cases):
    fac=dict(zip(ps,es));N=1
    for p,a in fac.items():N*=p**a
    S=support_lambda(fac)
    fp=fps[i%len(fps)]
    S.add(fp if fp not in S else 59)
    got,tested=recover(N,S)
    assert got==fac
    counts["inputs"]+=1;counts["vectors"]+=tested
    counts["factors"]+=len(fac);counts["false"]+=1
    counts["repeat"]+=sum(a>1 for a in es)
    counts["two"]+=int(2 in fac)

print(f"general advised inputs: {counts['inputs']}")
print(f"support vectors tested: {counts['vectors']}")
print(f"distinct factors recovered: {counts['factors']}")
print(f"repeated-prime components: {counts['repeat']}")
print(f"false-positive support cases: {counts['false']}")
print(f"inputs containing factor 2: {counts['two']}")
print("PASS")
