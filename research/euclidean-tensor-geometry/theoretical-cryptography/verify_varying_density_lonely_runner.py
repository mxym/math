#!/usr/bin/env python3
"""Exact finite controls for the varying-density random Lonely Runner proof."""
from collections import Counter
from fractions import Fraction as F
from math import ceil, comb, floor, gcd
from itertools import combinations,product


def need(test,msg):
    if not test: raise AssertionError(msg)


def cross(u,v):
    return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])


def dot(u,v):
    return sum(a*b for a,b in zip(u,v))


def signed(x,p):
    j=x%p
    return j-p if 2*j>p else j


def forbidden(N,p,a,delta):
    return {v for v in range(1,N+1) if abs(signed(a*v,p))*delta.denominator<delta.numerator*p}


def dimension(points):
    if not points:return 0,None
    u=points[0]
    n=next((t for v in points[1:] if any(t:=cross(u,v))),None)
    if n is None:return 1,None
    if any(dot(n,v) for v in points):return 3,None
    d=gcd(*n)
    return 2,tuple(x//d for x in n)


lattice=Counter()
for N,p in [(25,101),(43,211),(72,401),(25,1009)]:
    delta=F(N,p)
    for a in range(1,min(p,40)):
        A=forbidden(N,p,a,delta)
        for b in range(1,min(p,40)):
            B=forbidden(N,p,b,delta)
            pts=[(v,signed(a*v,p),signed(b*v,p)) for v in sorted(A&B)]
            dim,n=dimension(pts)
            lattice[dim]+=1
            if dim==2:
                need(gcd(*n)==1 and dot(n,(1,a,b))%p==0,"primitive normal and residue line")
                if n[2]%p:
                    need((-(n[0]+a*n[1])*pow(n[2],-1,p))%p==b,"normal determines b")
                else:
                    need(n[1]%p and signed(a*n[1],p)==signed(-n[0],p),"normal precludes a good a if short")
                for u,v in combinations(pts,2):
                    need(all(x%p==0 for x in cross(u,v)),"common rank-one reduction mod p")
need(len(lattice)==4,"all lattice-dimension regimes exercised")

grid=0
for T,Q,upper in [(257,10,6),(400,30,12),(510,28,34),(201,5,7)]:
    gridpts=set()
    cap=0
    for q in range(1,upper+1):
        for a in range(q):
            if gcd(a,q)!=1:continue
            around={k for k in range(T) if min((F(k,T)-F(a,q))%1,(F(a,q)-F(k,T))%1)<=F(1,q*Q)}
            need(len(around)<=1+F(2*T,q*Q),"circle grid cardinality")
            gridpts.update(around)
            cap+=1+F(2*T,q*Q)
            grid+=1
    need(len(gridpts)<=cap,"union of small-rational arcs")

prob=0
for N in [60,109,200]:
    for m in [3,12,21,N//2]:
        w=F(N-m,N)
        for b in range(0,N-m+1):
            p=F(comb(N-b,m),comb(N,m))
            q=w**b
            product_ratio=F(1)
            for j in range(b):
                product_ratio*=1-F(m*j,(N-m)*(N-j))
            need(0<=p<=q and p==q*product_ratio,"fixed-size avoidance factorization")
            prob+=1

for N,p,q in [(128,11,13),(400,13,17),(700,11,19)]:
    counts=[]
    for k,l in product(range(1,(p+1)//2),range(1,(q+1)//2)):
        v={k,0,-k%p};w={l,0,-l%q}
        direct=sum(i%p in v and i%q in w for i in range(1,N+1))
        need(direct<=9*(1+N//(p*q)),"CRT including p*q <= N")
        counts.append(direct)
    target=sum((1 if i%p==0 else F(2,p-1))*(1 if i%q==0 else F(2,q-1)) for i in range(1,N+1))
    need(sum(counts)==target*len(counts),"exact average distinct-prime intersection")
print("PASS lattice dimensions",sorted(lattice.items()),"grid",grid,"fixed-cardinality",prob)
