#!/usr/bin/env python3
"""Exact finite sanity replay of the ticket packing and product-law repair.
No third-party libraries. These cases do not replace the countable proof."""
from fractions import Fraction as F
from itertools import combinations
from collections import Counter

def require(test, msg):
    if not test:
        raise ArithmeticError(msg)

def pack(p,L,stats):
    pi=[F(1,s) for s in range(L,2*L)]; Z=sum(pi);pi=[v/Z for v in pi]
    m=len(p)
    require(sum(p)==1 and all(x>=0 for x in p),'input')
    tickets=[];a={};bits={};v={}
    for x,px in enumerate(p):
        if not px: continue
        b=0
        while px*(2**(b+1))<=1:b+=1
        v[x]=px*2**b;bits[x]=b; a[x]=int(L*v[x])-1
        require(F(1,2)<v[x]<=1 and a[x]>=1,'mantissa')
        for z in range(a[x],2*a[x]):
            earliest=(F(z+1)/v[x]).__ceil__()
            tickets.append((earliest,b,x,z))
    total=sum(F(1,2**e[1]) for e in tickets)
    require(L-4<=total<=L,'total')
    q={};escape=[];avail=[]; pending=sorted(tickets,reverse=True);dest={}
    for s in range(L,2*L):
        while pending and pending[-1][0]<=s:avail.append(pending.pop())
        require(sum(F(1,2**e[1]) for e in pending)<=2*L-1-s,'late volume')
        remaining=F(1); deferred=[]
        # fill with largest jobs first. A slot taken has a unique normal prefix
        # by cumulative Kraft packing. Reconstruct all continuations forward.
        for earliest,b,x,z in sorted(avail,key=lambda e:e[1]):
            w=F(1,2**b)
            if remaining<w:deferred.append((earliest,b,x,z));continue
            start=1-remaining
            require((start/w).denominator==1,'prefix alignment')
            remaining-=w
            require(z+1<=v[x]*s,'release')
            stack=[(z,0)]
            while stack:
                t,k=stack.pop()
                if t<L:
                    stack.extend(((2*t,k+1),(2*t+1,k+1)));continue
                require(t<2*L and (x,t) not in dest,'injectivity')
                dest[x,t]=(s,z,k);q[x,t]=pi[s-L]*w/2**k
        require(not deferred or remaining==0,'fill')
        avail=deferred;escape.append(remaining)
    require(not pending and not avail and sum(escape)==L-total,'coverage')
    gap=sum(z*w for z,w in zip(pi,escape))
    require(gap<=F(8,L) and sum(q.values())==1-gap,'escape total')
    deficits={}
    for x,px in enumerate(p):
        for t in range(L,2*L):
            r=px*pi[t-L]
            if px:
                s,z,k=dest[x,t]; u=t
                while u>=2*a[x]:u//=2
                require(u==z and u==t//2**k,'inverse')
            d=r-q.get((x,t),0)
            require(d>=0,'overweight')
            if gap:deficits[x,t]=d/gap
            if gap:require(q.get((x,t),0)+gap*deficits[x,t]==r,'product correction')
    if gap:require(sum(deficits.values())==1,'normalized law')
    stats['tables']+=1;stats['tickets']+=len(tickets);stats['normal pairs']+=len(q)
    stats['restored target/state pairs']+=m*L

def compositions(n,m):
    for anch in combinations(range(1,n),m-1):
        pts=(0,)+anch+(n,)
        yield tuple(F(b-a,n) for a,b in zip(pts,pts[1:]))

def main():
    stats=Counter()
    for L in (16,21,31):
        for m in (1,2,3,4):
            for p in compositions(9,m):pack(p,L,stats)
        for p in ((F(0),F(1,33),F(0),F(32,33)),(F(1,4097),F(4096,4097)),tuple([F(1,65)]*65)):
            pack(p,L,stats)
        # Long tail with many dyadic levels.
        p=tuple(F(1,2**k) for k in range(1,14))+(F(1,8192),)
        pack(p,L,stats)
    print('PASS:',', '.join('%s = %d'%(k,v) for k,v in stats.items()))
if __name__=='__main__':main()
