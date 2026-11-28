#!/usr/bin/env python3
from fractions import Fraction
from itertools import combinations, product
from math import gcd, factorial, isqrt

def primes_upto(n):
    a=[True]*(n+1)
    a[0]=a[1]=False
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=[False]*(((n-p*p)//p)+1)
    return [i for i,v in enumerate(a) if v]

PR=primes_upto(80)

def val(fac):
    z=1
    for p,a in fac: z*=p**a
    return z

def phi(fac):
    z=1
    for p,a in fac: z*=p**(a-1)*(p-1)
    return z

def geom(p,m):
    return (p**m-1)//(p-1)

def sigpow(fac,T):
    z=1
    for p,a in fac: z*=geom(p,a*T+1)
    return z

def clog2(n):
    return (n-1).bit_length()

def structure(fac):
    n=val(fac); ph=phi(fac); M=clog2(n)
    R=n//gcd(n,ph)
    U=gcd(n,R**M); V=n//U
    groups={}
    unknown=[]
    for p,a in fac:
        if R%p==0: groups.setdefault(a,[]).append(p)
        else: unknown.append((p,a))
    assert groups and U*V==n
    assert R==prod(p for ps in groups.values() for p in ps)
    return n,ph,M,R,U,V,groups,unknown

def prod(xs):
    z=1
    for x in xs: z*=x
    return z

coprime_cases=0
for K in range(3,11):
    r=K-2; L=factorial(K-2)
    for M in range(2,31):
        J=L*((max(2,M)+L-1)//L)
        for a in range(1,M+1):
            ms=[a*i*J+1 for i in range(1,r+1)]
            for x,y in combinations(ms,2):
                assert gcd(x,y)==1
                coprime_cases+=1

totient_cases=0
normalized_phi_cases=0
structure_cases=0
for k in range(1,6):
    for ps in combinations(PR[:7],k):
        for exps in product(range(1,4),repeat=k):
            fac=list(zip(ps,exps))
            n,ph,M,R,U,V,groups,unknown=structure(fac)
            T=max(2,M)
            assert n**(T+1)//sigpow(fac,T)==ph
            totient_cases+=1
            structure_cases+=1
            lhs=1
            signbase=1
            for a,qs in groups.items():
                u=prod(qs)
                P1=prod(1-q for q in qs)
                lhs*=P1
                signbase*=((-1)**len(qs))*u
            for x,b in unknown:
                lhs*=x-1
            C=Fraction(ph,n)*signbase
            rhs=C*prod(x for x,b in unknown)
            assert Fraction(lhs,1)==rhs
            normalized_phi_cases+=1

def compositions(n,k):
    if k==1:
        yield (n,); return
    for a in range(1,n-k+2):
        for tail in compositions(n-a,k-1):
            yield (a,)+tail

boundary_cases=0
adaptive_budget_guesses=0
for K in range(3,11):
    for k in range(1,K+1):
        for h in range(0,k+1):
            known=k-h
            if known<1: continue
            for g in range(1,known+1):
                for ks in compositions(known,g):
                    B=max(1,k-g-1 if h==0 else k-g-2)
                    assert 1<=B<=K-2
                    adaptive_budget_guesses+=1
                    if h==0 and g==1:
                        cap=k-3
                        assert B>cap
                        boundary_cases+=1
                        continue
                    if h>=2:
                        cap=k-g-3
                        assert B>cap
                        boundary_cases+=1
                    if h>0 and any(t>=2 for t in ks):
                        cap=k-g-3
                        assert B>cap
                        boundary_cases+=1
                    if h==0 and g>=2 and any(t>=2 for t in ks):
                        cap=k-g-2
                        assert B>cap
                        boundary_cases+=1

samples=[
    (5,[(5,1),(7,1),(13,1),(17,2),(23,2)]),
    (5,[(7,1),(11,1),(2,1),(3,2),(5,3)]),
    (6,[(2,1),(3,2),(5,3),(7,1),(11,2),(13,3)]),
    (7,[(2,2),(3,2),(5,1),(7,3),(11,1),(13,2)])
]
query_identities=0
adaptive_samples=0
for K,fac in samples:
    n,ph,M,R,U,V,groups,unknown=structure(fac)
    B=max(1,len(fac)-len(groups)-1 if not unknown else len(fac)-len(groups)-2)
    assert B<=K-2
    r=B; L=factorial(K-2); J=L*((max(2,M)+L-1)//L)
    adaptive_samples+=1
    for i in range(1,r+1):
        S=sigpow(fac,i*J)
        rhs=1
        for p,a in fac: rhs*=geom(p,a*i*J+1)
        assert S==rhs
        query_identities+=1

def primitive_root(p):
    x=p-1; fs=[]; d=2
    while d*d<=x:
        if x%d==0:
            fs.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fs.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise AssertionError

def pmul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%p
    return tuple(c)

uniform_boundary_points=0
for p,ms in [(31,(2,3,5)),(4219,(19,37))]:
    g=primitive_root(p)
    sets=[]
    for m in ms:
        assert (p-1)%m==0
        roots={pow(g,(p-1)*j//m,p) for j in range(1,m)}
        assert len(roots)==m-1 and 1 not in roots
        sets.append(sorted(roots))
    polys=set()
    for zs in product(*sets):
        q=(p-1,1) # Z-1
        for z in zs: q=pmul(q,((p-z)%p,1),p)
        polys.add(q)
    want=prod(m-1 for m in ms)
    assert len(polys)==want
    uniform_boundary_points+=want

print("PASS")
print("pairwise effective-index pairs:",coprime_cases)
print("totient-floor cases:",totient_cases)
print("exact structural-split cases:",structure_cases)
print("normalized-totient identities:",normalized_phi_cases)
print("strengthened boundary-budget cases:",boundary_cases)
print("adaptive-budget structural guesses:",adaptive_budget_guesses)
print("adaptive mixed samples:",adaptive_samples)
print("true sparse-query identities:",query_identities)
print("uniform boundary points:",uniform_boundary_points)
