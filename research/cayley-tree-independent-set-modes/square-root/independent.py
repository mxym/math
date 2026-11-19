#!/usr/bin/env python3
"""Enumerate trees as acyclic edge subsets (not Prüfer words), exact labeled balls
(no automorphism normalization), exact hard-core p from all subsets versus ball recursion."""
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
from math import prod
def chk(b,m):
    if not b:raise ValueError(m)
def trees(n):
    for es in combinations(combinations(range(n),2),n-1):
        ix=list(range(n))
        def parent(i):
            while i!=ix[i]:i=ix[i]
            return i
        for u,v in es:
            a,b=parent(u),parent(v)
            if a==b:break
            ix[a]=b
        else:
            g=[[] for _ in range(n)]
            for u,v in es:g[u].append(v);g[v].append(u)
            yield es,g
def dist(g,r):
    a=[-1]*len(g);a[r]=0;q=[r]
    for v in q:
        for w in g[v]:
            if a[w]==-1:a[w]=a[v]+1;q.append(w)
    return a
def ball(r,h,a,es):
    V=tuple(i for i,v in enumerate(a) if v<=h)
    E=tuple((u,v) for u,v in es if a[u]<=h and a[v]<=h)
    b=a.count(h)
    return r,h,V,E,b
def marklabelcount(key,n):
    T=sum(len(x[2]) for x in key);bs=[x[-1] for x in key];m=len(key);U=T-sum(bs)
    if any(b==0 for b in bs):
        chk(m==1 and T==n,'zero boundary disconnected')
        return 1
    return prod(bs)*F(n-U)**(n-T+m-2)
def odds(g,v,parent,h):
    if h==0:return F(0)
    return prod((1/(1+odds(g,u,v,h-1)) for u in g[v] if u!=parent),start=F(1))
def go(n):
    C=Counter();N=pchecks=0
    for es,g in trees(n):
        N+=1; ds=[dist(g,v) for v in (0,1)];bs=[[ball(v,h,ds[v],es) for h in range(3)] for v in (0,1)]
        for A in bs[0]:
            C[(A,)]+=1
            for B in bs[1]:
                if set(A[2]).isdisjoint(B[2]):C[(A,B)]+=1
        good=[m for m in range(1<<n) if all(((m>>u)&1)*((m>>v)&1)==0 for u,v in es)]
        for v in (0,1):
            p=F(sum((m>>v)&1 for m in good),len(good))
            old=F(0)
            for h in range(1,max(ds[v])+2):
                x=odds(g,v,-1,h);H=x/(1+x)
                # log(2)<7/10 (e^(7/10)>2), so this tests a slightly enlarged rational bound.
                chk(abs(H-old)<=F(7,10*2**(h-1))*ds[v].count(h-1),'stabilization')
                old=H;pchecks+=1
            chk(old==p,'exact occupation')
    chk(N==n**(n-2),'not every tree')
    t=Counter()
    for k,freq in C.items():
        guess=marklabelcount(k,n)
        chk(guess==freq,('fixed labeled ball count',k,freq,guess))
        t[len(k)]+=1
    print('n',n,'labeled trees',N,'one-root cases',t[1],'ordered two-root cases',t[2],'message comparisons',pchecks)
if __name__=='__main__':
    for n in range(2,7):go(n)
    print('PASS')
