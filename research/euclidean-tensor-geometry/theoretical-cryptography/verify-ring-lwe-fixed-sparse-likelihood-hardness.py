#!/usr/bin/env python3
"""Finite identities on preset toy data; no decoding or optimization."""
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt
from random import Random

def positions(n):
    def prime(x):
        return all(x % j for j in range(2,isqrt(x)+1))
    p = next(x for x in range(n+1,2*n) if prime(x))
    return [2*p*i+i*i%p for i in range(n)]

def mono(e,d):
    return e%d, (-1 if (e//d)%2 else 1)

def mul(a,b,d,q):
    out = [0]*d
    for i,x in a.items():
        for j,y in b.items():
            r, sign = mono(i+j,d)
            out[r] = (out[r]+sign*x*y)%q
    return {i:x for i,x in enumerate(out) if x}

def base(i,j,d,u=1):
    a,ea=mono(-i,d)
    b,eb=mono(-j,d)
    assert a != b
    return {a:ea*u,b:-eb*u}

def shifted(v,t,q):
    out = [0]*len(v)
    for j,x in enumerate(v):
        r, sign = mono(j+t,len(v))
        out[r] = sign*x%q
    return out

gapchecks=unitchecks=designchecks=scorechecks=roundchecks=0
for n in (4,8,16,32,64,128,256):
    p=positions(n)
    gaps=[j-i for i,j in combinations(p,2)]
    assert len(set(gaps))==len(gaps) and min(gaps)>0
    d=16*n*n
    assert 2*max(p)<d
    gapchecks+=len(gaps)
for d in (4,8,16,32,64,128,256):
    for q in (3,5,7,11):
        for a in range(1,d):
            for e in (-1,1):
                stop=d//gcd(a,d)
                inv={}
                for k in range(stop):
                    j,s=mono(k*a,d)
                    assert j not in inv
                    inv[j]=s*e**k%q
                assert mul({0:1,a:-e},inv,d,q)=={0:2}
                unitchecks+=1
for n in (4,8,16,32):
    p=positions(n)
    d=16*n*n
    seen=set()
    t=0
    for i,j in combinations(range(n),2):
        a=base(p[i],p[j],d)
        for _ in range(6):
            b=tuple(sorted(mul({t:1},a,d,3)))
            assert b not in seen and len(b)==2
            seen.add(b)
            assert min(b[1]-b[0],d-b[1]+b[0])==p[j]-p[i]
            assert t<d
            t+=1
    designchecks+=t

rng=Random(17)
for q in (3,5,7):
    d=32
    # The two coordinates and row shifts are fixed artificial data.
    i,j=3,12
    h=[41]+[12-min(c,q-c)**2 for c in range(1,q)]
    H=sum(h)
    kap=q*(q*h[0]-H)
    for repeat in range(2):
        for z in range(q):
            s=[rng.randrange(q) for _ in range(d)]
            s[i]=(s[j]+z)%q
            sp={j:x for j,x in enumerate(s) if x}
            for active in (False,True):
                got=0
                for u in range(1,q):
                    a=base(i,j,d,u)
                    grid=mul(a,sp,d,q)
                    assert grid.get(0,0)==u*z%q
                    targets=([c for c in range(1,q) for _ in range(q)] if active else
                             [c for c in range(q) for _ in range(q-1)])
                    for t,c in enumerate(targets):
                        y=[c]+[t%q]*(d-1)
                        t2=(t*7+u*11+repeat)%d
                        ash=mul({t2:1},a,d,q)
                        product=mul(ash,sp,d,q)
                        ysh=shifted(y,t2,q)
                        ls=sum(h[(x-product.get(j,0))%q] for j,x in enumerate(ysh))
                        assert ls==sum(h[(x-grid.get(j,0))%q] for j,x in enumerate(y))
                        got+=ls
                        scorechecks+=1
                nuisance=(d-1)*(q-1)**2*H
                exp=(nuisance+q*(q-1)*(H-h[0])+kap*(z!=0)
                     if active else nuisance+(q-1)**2*H)
                assert got==exp
for n in (4,8):
    p=positions(n)
    d=16*n*n
    L=n*(n-1)//2
    for rep in range(8):
        s=[rng.randrange(3) for _ in range(d)]
        sp={j:a for j,a in enumerate(s) if a}
        T=M=U=D=0
        for i,j in combinations(range(n),2):
            typ=rng.randrange(4)
            if typ==3:
                targets=[0,0,1,1,2,2]
            else:
                targets=[c for c in range(3) if c!=typ for _ in range(3)]
                M+=1
                U+=(s[p[i]]-s[p[j]])%3 != typ
            for r,c in enumerate(targets):
                a=mul({T:1},base(p[i],p[j],d),d,3)
                y=shifted([c]+[r%3]*(d-1),T,3)
                prod=mul(a,sp,d,3)
                D+=sum(x!=prod.get(j,0) for j,x in enumerate(y))
                T+=1
                scorechecks+=1
        assert T==6*L and D==L*(4*d+2)-2*(L-M)-3*U

# Independent finite rational rounding checks over given evaluation events.
for S in range(1,18):
    for _ in range(70):
        nums=[rng.randrange(1,30) for _ in range(S)]
        weights=[Fraction(a,sum(nums)) for a in nums]
        K=73*S
        exact=[a*K for a in weights]
        v=[a.numerator//a.denominator for a in exact]
        for i in sorted(range(S),key=lambda i:exact[i]-v[i],reverse=True)[:K-sum(v)]:
            v[i]+=1
        assert sum(v)==K
        E={i for i in range(S) if rng.randrange(2)}
        assert all(abs(v[i]-exact[i])<1 for i in range(S))
        assert abs(sum(weights[i] for i in E)-Fraction(sum(v[i] for i in E),K))<=Fraction(S,K)
        roundchecks+=1
print("PASS separations / units / distinct designed rows / score rows / rounding:",gapchecks,unitchecks,designchecks,scorechecks,roundchecks)
