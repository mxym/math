#!/usr/bin/env python3
"""Synthetic exact checks of mixed Gaussian polynomial elimination."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial
from random import Random
from sympy import Matrix

rng=Random(34636)
log=Counter()
box=(-1,0,1)
NDEG=6


def clean(d):
    return {k:v for k,v in d.items() if v}


def mul(a,b):
    c=Counter()
    for x,v in a.items():
        for y,w in b.items():
            if x[0]+y[0]<=NDEG:
                c[tuple(p+q for p,q in zip(x,y))]+=v*w
    return clean(c)


def shiftadd(a,b,c=F(1)):
    o=Counter(a)
    for x,v in b.items():
        o[x]+=v*c
    return clean(o)


def from_linear(f,rr,tdegree=0):
    p={}
    for j,v in f.items():
        t=[tdegree]+[0]*rr
        t[j+1]=1
        p[tuple(t)]=v
    return clean(p)


def split(n,forms,cut):
    adj=[[] for _ in range(n)]
    pins=set()
    for w,l in forms:
        if w<cut:
            continue
        if len(l)==1:
            pins.update(l)
        else:
            (a,s),(b,t)=list(l.items())
            adj[a].append((b,-s*t))
            adj[b].append((a,-s*t))
    seen=set()
    comps=[]
    for i in range(n):
        if i in seen:
            continue
        signs={i:1}
        q=[i]
        good=True
        while q:
            j=q.pop()
            for a,s in adj[j]:
                must=signs[j]*s
                if a in signs:
                    good=good and must==signs[a]
                else:
                    signs[a]=must
                    q.append(a)
        seen.update(signs)
        if good and not set(signs)&pins:
            comps.append(signs)
    roots={min(s) for s in comps}
    ys=[v for v in range(n) if v not in roots]
    zs=[next(((i,s[v]) for i,s in enumerate(comps) if v in s),None)
        for v in range(n)]
    layers=[]
    for w,l in forms:
        y,z={},Counter()
        for i,b in l.items():
            if i in ys:
                y[ys.index(i)]=b
            if zs[i] is not None:
                j,c=zs[i]
                z[j]+=b*c
        z=clean(z)
        assert (w<cut or not z) and sum(b*b for b in z.values())<=4
        layers.append((w,y,z))
    return ys,zs,len(comps),layers


def polys(ys,rr,layers):
    d=len(ys)
    z0=(0,)*(rr+1)
    fac=[]
    for w,lz,rz in layers:
        yscope=tuple(lz)
        scope=set(yscope)|{d+j for j in rz}
        Q={}
        for i,ci in rz.items():
            for j,cj in rz.items():
                if i<=j:
                    Q[i,j]=w*ci*cj*(1+int(i!=j))
        tab={}
        for vals in product(box,repeat=len(yscope)):
            yv=sum(lz[i]*v for i,v in zip(yscope,vals))
            # Synthetic rational nonnegative table, independent of Gaussian weights.
            base=F(2,3)**(yv*yv)
            atom=from_linear({j:-2*w*yv*c for j,c in rz.items()},rr,1)
            out=exp={z0:base}
            for k in range(1,NDEG+1):
                exp={x:k0/k for x,k0 in mul(exp,atom).items()}
                out=shiftadd(out,exp)
            tab[vals]=out
        fac.append((scope,yscope,Q,tab))
    return fac


def elim(d,rr,fs,order):
    one={(0,)*(rr+1):F(1)}
    prod_pivot=F(1)
    for i in order:
        take=[f for f in fs if i in f[0]]
        fs=[f for f in fs if i not in f[0]]
        if not take:
            assert i<d
            fs.append((set(),(),{}, {():{(0,)*(rr+1):F(len(box))}}))
            continue
        scope=set().union(*(f[0] for f in take))
        yc=tuple(sorted(j for j in scope if j<d))
        Q={}
        for _,_,q,_ in take:
            Q=shiftadd(Q,q)
        out={}
        if i>=d:
            v=i-d
            a=Q[v,v]
            assert a>0
            prod_pivot*=a
            bs={j:Q.get((min(j,v),max(j,v)),F(0))/2
                for j in range(rr) if j!=v and d+j in scope}
            newQ={k:c for k,c in Q.items() if v not in k}
            for j,b in bs.items():
                for l,c in bs.items():
                    if j<=l:
                        newQ=shiftadd(newQ,{(j,l):-b*c*(1+int(j!=l))/a})
            Q=newQ
            lin=from_linear({j:-b/a for j,b in bs.items()},rr)
            powers=[one]
            for h in range(1,NDEG+1):
                powers.append(mul(powers[-1],lin))
            stats=[]
            even=F(1)
            for h in range(NDEG//2+1):
                if h:
                    even*=F(2*h-1)/(2*a)
                stats.append(even)
        newyc=tuple(z for z in yc if z!=i)
        for vals in product(box,repeat=len(yc)):
            y=dict(zip(yc,vals))
            z=one
            for _,fc,_,t in take:
                z=mul(z,t[tuple(y[j] for j in fc)])
            if i<d:
                tt=z
            else:
                tt={}
                for k,c in z.items():
                    h=k[1+v]
                    b=list(k)
                    b[1+v]=0
                    for j in range(h//2+1):
                        tt=shiftadd(tt,mul({tuple(b):c},powers[h-2*j]),
                                     F(comb(h,2*j))*stats[j])
            at=tuple(y[j] for j in newyc)
            out[at]=shiftadd(out.get(at,{}),tt)
        fs.append((scope-{i},newyc,Q,out))
        log["mixed buckets"]+=1
    poly=one
    for scope,yc,Q,tab in fs:
        assert not scope and not yc and not Q
        poly=mul(poly,tab[()])
    return poly,prod_pivot


def test(n,forms,cut):
    ys,zs,r,layers=split(n,forms,cut)
    d=len(ys)
    A=Matrix(r,r,lambda i,j:sum(w*z.get(i,0)*z.get(j,0) for w,y,z in layers))
    L=Matrix(r,d,lambda i,j:sum(w*z.get(i,0)*y.get(j,0) for w,y,z in layers))
    Ss=L.T*A.inv()*L if r else Matrix.zeros(d,d)
    all0=(0,)*r
    direct=Counter()
    for vals in product(box,repeat=d):
        v=Matrix(d,1,vals)
        u=F((v.T*Ss*v)[0])
        yvs=[sum(c*vals[j] for j,c in y.items()) for w,y,z in layers]
        b=F(2,3)**sum(t*t for t in yvs)
        for t in range(NDEG//2+1):
            direct[(2*t,)+all0]+=b*u**t/factorial(t)
        assert 0<=u<=sum(w*v*v for v,(w,y,z) in zip(yvs,layers) if w<cut)
        assert sum(w*v*v for v,(w,y,z) in zip(yvs,layers) if w>=cut)*4*n*n>=cut*sum(t*t for t in vals)
        for vs in (all0,tuple(rng.choice(box) for _ in range(r))):
            x=[]
            for i in range(n):
                yi=vals[ys.index(i)] if i in ys else 0
                x.append(yi if zs[i] is None else yi+zs[i][1]*vs[zs[i][0]])
            assert [sum(c*x[i] for i,c in l.items()) for w,l in forms] == [
                val+sum(c*vs[j] for j,c in z.items()) for val,(w,y,z) in zip(yvs,layers)]
            log["integral substitution rows"]+=1
    fac=polys(ys,r,layers)
    for order in (list(range(d+r)),rng.sample(range(d+r),d+r)):
        value,D=elim(d,r,fac,order)
        assert value==clean(direct),(n,forms,order,value,clean(direct))
        assert D==A.det()
        log["exact Gaussian Taylor polynomials"]+=1
    return r,Ss


cut=F(1,2)
b=F(1,83)
for h in range(1,5):
    fs=[(F(1),{i:1,h+i:-1}) for i in range(h)]
    fs += [(b,{i:1}) for i in range(h,h+h)]
    fs += [(b,{i:1,i+1:-1}) for i in range(h-1)]
    r,Ss=test(2*h,fs,cut)
    assert r==h and Ss.rank()==h and all(x>0 for x in Ss)
    log["dense full-rank Schur examples"]+=1
for trial in range(24):
    n=rng.randrange(2,6)
    fs=[(b,{i:1}) for i in range(n)]
    for j,k in combinations(range(n),2):
        if rng.random()<.4:
            fs.append((rng.choice((b,F(1),F(8,7))),{j:1,k:rng.choice((-1,1))}))
    if trial%3==0:
        fs.append((F(1),{0:1}))
    if trial%7==0 and n>=3:
        fs += [(F(2),{0:1,1:-1}),(F(2),{1:1,2:-1}),(F(2),{0:1,2:1})]
    test(n,fs,cut)
for p in (0,3,9,80):
    for n in range(1,8):
        for m in range(1,8):
            K=64*(m+1)*(n+p+10)
            q=F(1,2**(K//(4*m)))
            assert (1+2*q/(1-q))**n-1 < F(1,2**(p+10))
            log["Poisson-tail bounds"]+=1
print("PASS multiscale Gaussian elimination:",dict(log))
