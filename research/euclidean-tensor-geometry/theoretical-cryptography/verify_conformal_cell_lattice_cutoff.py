#!/usr/bin/env python3
"""Finite exact checks of conformal cell motion in known mathematical energies."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd
from random import Random


def dot(a,x):
    return sum(z*t for z,t in zip(a,x))


def signs(M,y):
    return tuple((d>0)-(d<0) for d in (dot(a,y) for a in M))


def conforms(M,s,r):
    for a,b in zip(M,s):
        d=dot(a,r)
        if (d*b<0) or (b==0 and d!=0):
            return False
    return True


def rays2(A):
    M=[(1,0),(0,1)]+list(A)
    R=set()
    for a,b in M:
        d=gcd(a,b)
        if d:
            r=(b//d,-a//d)
            R.update((r,(-r[0],-r[1])))
    return M,sorted(R)


def cell2(M,R,y):
    s=signs(M,y)
    rr=[r for r in R if conforms(M,s,r)]
    assert 1<=len(rr)<=2
    if len(rr)==1:
        r=rr[0]
        k=0 if r[0] else 1
        alpha=[y[k]/r[k]]
    else:
        (a,b),(c,d)=rr
        det=a*d-b*c
        assert det!=0
        alpha=[(d*y[0]-c*y[1])/det,(a*y[1]-b*y[0])/det]
    assert all(v>0 for v in alpha)
    assert tuple(sum(a*r[k] for a,r in zip(alpha,rr)) for k in range(2))==y
    return rr,alpha


def two_dimensional():
    rng=Random(251)
    total=cases=multiple=0
    for it in range(36):
        A=[(rng.randrange(-3,4),rng.randrange(-3,4)) for _ in range(3)]
        M,R=rays2(A)
        h=1+it%2
        W=[F(rng.randrange(1,10),7) for i in M]
        if it%2:
            W[0]+=2**120
        C=max(max(map(abs,r)) for r in R)
        images=Counter()
        for x in product(range(-2*C*h-4,2*C*h+5),repeat=2):
            y=(F(x[0])-F(it%3,3), F(x[1])+F(it%5,5))
            if max(map(abs,y))<=2*C*h:
                continue
            rr,alpha=cell2(M,R,y)
            i=next(i for i,a in enumerate(alpha) if a>h)
            z=rr[i]
            u=tuple(v-h*t for v,t in zip(y,z))
            assert signs(M,y)==signs(M,u)
            sr,beta=cell2(M,R,u)
            assert rr==sr and beta==[a-h*(k==i) for k,a in enumerate(alpha)]
            for p in (1,2,4):
                delta=sum(w*(abs(dot(a,y))**p-abs(dot(a,u))**p)
                          for a,w in zip(M,W))
                lower=sum(w*abs(h*dot(a,z))**p for a,w in zip(M,W))
                assert delta>=lower>0
            images[u]+=1
            total+=1
        assert max(images.values())<=2
        multiple+=sum(c>1 for c in images.values())
        cases+=1
    assert multiple>0
    return total,cases,multiple


def nonsimplicial():
    r00,r10,r01,r11=(0,0,1),(1,0,1),(0,1,1),(1,1,1)
    rows=[(1,0,0),(0,1,0),(0,0,1),(-1,0,1),(0,-1,1)]

    def cell(y):
        x,v,w=y
        if x>=v:
            d=[(r00,w-x),(r10,x-v),(r11,v)]
        else:
            d=[(r00,w-v),(r01,v-x),(r11,x)]
        assert all(a>=0 for r,a in d)
        return [(r,a) for r,a in d if a]

    cases=0
    for j in range(1,33):
        w=F(j,3)
        for k,l in product(range(j+1),repeat=2):
            y=(F(k,3),F(l,3),w)
            if w<=3:
                continue
            d=cell(y)
            p=next(i for i,(r,a) in enumerate(d) if a>1)
            z=d[p][0]
            u=tuple(v-t for v,t in zip(y,z))
            assert signs(rows,y)==signs(rows,u)
            assert cell(u)==[(r,a-(i==p)) for i,(r,a) in enumerate(d)]
            assert sum(dot(r,y)**2-dot(r,u)**2 for r in rows)>=sum(
                        dot(r,z)**2 for r in rows)
            cases+=1
    return cases


def det(a):
    a=[list(map(F,row)) for row in a]
    n=len(a)
    d=F(1)
    for i in range(n):
        p=next((k for k in range(i,n) if a[k][i]),None)
        if p is None:
            return 0
        if i!=p:
            a[i],a[p]=a[p],a[i]
            d=-d
        z=a[i][i]
        d*=z
        for p in range(i+1,n):
            w=a[p][i]/z
            if w:
                for h in range(i+1,n):
                    a[p][h]-=w*a[i][h]
    return d


def interval_minors():
    count=0
    for n in range(1,7):
        A=[tuple(int(i<=x<j) for x in range(n)) for i in range(n)
           for j in range(i+1,min(n,i+3)+1)]
        for B in combinations(A,n):
            assert abs(det(B))<=1
            count+=1
    return count


if __name__=="__main__":
    print("PASS: planar moves/fans/multiple fibers, nonsimplicial cell moves, interval minors")
    print(*two_dimensional(),nonsimplicial(),interval_minors())
