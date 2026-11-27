#!/usr/bin/env python3
"""Exact generated checks for rank-conditioned entry transport."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import prod


def rank(a, p):
    a = [list(v) for v in a]
    if not a:
        return 0
    k = 0
    for j in range(len(a[0])):
        h = next((i for i in range(k, len(a)) if a[i][j] % p), None)
        if h is None:
            continue
        a[k], a[h] = a[h], a[k]
        z = pow(a[k][j] % p, -1, p)
        a[k] = [v*z % p for v in a[k]]
        for i in range(k+1, len(a)):
            z = a[i][j] % p
            if z:
                a[i] = [(v-z*w) % p for v,w in zip(a[i],a[k])]
        k += 1
        if k == len(a):
            break
    return k


def mat(values, m):
    return [tuple(values[i:i+m]) for i in range(0,len(values),m)]


def unrank(v, p, n):
    a = []
    for _ in range(n):
        a.append(v % p)
        v //= p
    return a


def fourier2(v):
    a=list(v)
    d=1
    while d<len(a):
        for i in range(0,len(a),2*d):
            for j in range(i,i+d):
                x,y=a[j],a[j+d]
                a[j],a[j+d]=x+y,x-y
        d *= 2
    return a


def fourier3(v):
    # a+b*w in the exact ring with w^2+w+1=0
    a=[(z,0) for z in v]
    def omega(z):
        u,v=z
        return -v,u-v
    def total(*args):
        return tuple(sum(a) for a in zip(*args))
    d=1
    while d < len(a):
        for i in range(0,len(a),3*d):
            for j in range(i,i+d):
                x,y,z=a[j],a[j+d],a[j+2*d]
                wy,wz=omega(y),omega(z)
                a[j]=total(x,y,z)
                a[j+d]=total(x,wy,omega(wz))
                a[j+2*d]=total(x,omega(wy),wz)
        d *= 3
    return a


fourier_counts = reciprocal_counts = 0
for p,r,m in [(2,1,5),(2,2,4),(2,3,4),(3,1,4),(3,2,3),(3,3,3)]:
    n=r*m
    vals=[unrank(z,p,n) for z in range(p**n)]
    ranks=[rank(mat(x,m),p) for x in vals]
    for k in range(r+1):
        f=[int(s==k) for s in ranks]
        fft=(fourier2 if p==2 else fourier3)(f)
        levels={}
        for s,v in zip(ranks,fft):
            assert levels.setdefault(s,v)==v
            fourier_counts += 1
        assert fft[0] == (sum(f) if p==2 else (sum(f),0))
        if k>0:
            nn=sum(f)
            recip=sum((F(1,sum(x!=0 for x in z))
                       for z,j in zip(vals,ranks) if j==k),F(0))/nn
            assert recip <= F(5,r*m)
            reciprocal_counts += 1


rank_checks=edge_checks=0
for p,r,m in [(2,1,2),(2,1,5),(2,2,2),(2,2,4),(2,3,3),(2,3,4),
              (3,1,3),(3,2,2),(3,2,3),(3,2,4)]:
    n=r*m
    vals=[unrank(z,p,n) for z in range(p**n)]
    rankvals=[rank(mat(x,m),p) for x in vals]
    up,down={},{}
    powers=[p**j for j in range(n)]
    def update(z,pos,delta):
        old=vals[z][pos]
        return z+(((old+delta)%p)-old)*powers[pos]
    for z,rr in enumerate(rankvals):
        X=mat(vals[z],m)
        neighbors=[update(z,pos,s) for pos in range(n) for s in range(1,p)]
        u=[y for y in neighbors if rankvals[y]==rr+1]
        d=[y for y in neighbors if rankvals[y]==rr-1]
        up[z],down[z]=u,d
        included_i=[rank([row+(int(i==h),) for h,row in enumerate(X)],p)==rr
                    for i in range(r)]
        included_j=[rank(X+[tuple(int(j==l) for l in range(m))],p)==rr
                    for j in range(m)]
        assert len(u)==(p-1)*included_i.count(False)*included_j.count(False)
        if any(included_i) and any(included_j):
            witnesses={}
            for v in product(range(p),repeat=m):
                y=tuple(sum(a*b for a,b in zip(row,v))%p for row in X)
                if sum(y)==1 and y.index(1) not in witnesses:
                    witnesses[y.index(1)]=v
            formula=[update(z,i*m+j,-pow(witnesses[i][j],-1,p))
                     for i in range(r) for j in range(m)
                     if included_i[i] and included_j[j] and witnesses[i][j]]
            assert set(formula)==set(d)
        else:
            assert not d
        rank_checks += len(neighbors)
    # Defect-many exact coordinate changes to some full matrix.
    for k in range(r+1):
        for z in (x for x,rank_x in enumerate(rankvals) if rank_x==k):
            y=z
            while up[y]:
                y=up[y][0]
            assert rankvals[y]==r
            assert sum(a!=b for a,b in zip(vals[y],vals[z]))==r-k
    for k in range(r):
        source=[z for z,rr in enumerate(rankvals) if rr==k]
        target=[z for z,rr in enumerate(rankvals) if rr==k+1]
        E=sum(len(up[z]) for z in source)
        assert E==sum(len(down[z]) for z in target)>0
        flow=defaultdict(F)
        biased=defaultdict(F)
        for z in source:
            for y in up[z]:
                flow[y] += F(1,len(source)*len(up[z]))
                biased[y] += F(1,E)
                edge_checks += 1
        assert sum(flow.values())==sum(biased.values())==1
        assert all(biased[y]==F(len(down[y]),E) for y in target)
        tv=sum((abs(flow[y]-F(1,len(target))) for y in target),F(0))/2
        a=sum((abs(F(len(up[z]),E)-F(1,len(source))) for z in source),F(0))/2
        b=sum((abs(F(len(down[y]),E)-F(1,len(target))) for y in target),F(0))/2
        assert tv <= a+b


def normalize(d):
    mass = sum(d.values())
    return {x:v/mass for x,v in d.items()}


def quantile_coupling(a,b):
    a,b=sorted(a.items()),sorted(b.items())
    i=j=0
    x,w=a[i]
    y,v=b[j]
    out={}
    while i<len(a) and j<len(b):
        h=min(w,v)
        assert h>0
        out[x,y]=h
        w-=h
        v-=h
        if w==0:
            i+=1
            if i<len(a):
                x,w=a[i]
        if v==0:
            j+=1
            if j<len(b):
                y,v=b[j]
    assert i==len(a) and j==len(b)
    return out


def block_law(laws, target):
    nodes = product(*(list(A) for A in laws))
    return normalize({z:prod(A[x] for A,x in zip(laws,z))
                      for z in nodes if sum(z)%2==target})


def block_lift(laws, a, b):
    if a==b:
        return {(x,x):p for x,p in block_law(laws,a).items()}
    if len(laws)==1:
        return {(x,y):p for (x,y),p in
                quantile_coupling(block_law(laws,a),block_law(laws,b)).items()}
    def state(law):
        m=defaultdict(F)
        for z,p in law.items():
            m[sum(z[:-1])%2,z[-1]%2]+=p
        return m
    pairs=quantile_coupling(state(block_law(laws,a)),state(block_law(laws,b)))
    out=defaultdict(F)
    for ((e,f),(g,h)),w in pairs.items():
        for (x,y),u in block_lift(laws[:-1],e,g).items():
            for (v,z),t in block_lift(laws[-1:],f,h).items():
                out[x+v,y+z] += w*u*t
    return out


def gauss(a,c,B):
    return normalize({x:a**((2*x-c)**2) for x in range(-B,B+1)})


parities=0
for a0,a1 in [(F(2,3),F(3,4)),(F(9,10),F(7,8)),(F(1,2),F(4,5))]:
    for c0,c1 in [(-3,1),(0,0),(1,2),(3,-1)]:
        base=[gauss(a0,c0,3),gauss(a1,c1,2),gauss(F(4,5),1,2)]
        for n in (1,2,3):
            A,B=block_law(base[:n],0),block_law(base[:n],1)
            T=block_lift(base[:n],0,1)
            L,R=defaultdict(F),defaultdict(F)
            for (x,y),w in T.items():
                assert sum(abs(u-v) for u,v in zip(x,y))==1
                L[x]+=w
                R[y]+=w
                parities+=1
            assert dict(L)==A and dict(R)==B

print("PASS Fourier orbit samples",fourier_counts,"inverse weights",reciprocal_counts)
print("PASS rank/flip identities",rank_checks,"edge counts",edge_checks)
print("PASS exact rational parity couplings, transported atoms",parities)
