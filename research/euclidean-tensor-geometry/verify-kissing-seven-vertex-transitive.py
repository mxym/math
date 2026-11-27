#!/usr/bin/env python3
"""Exact product-sphere Delsarte chart verifier. Standard library only."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb,lcm
from pathlib import Path
import json,sys
if not __debug__:raise RuntimeError("assertions required")
@lru_cache(None)
def invbern(d):
    if d==0:return [[F(1)]]
    M=[]
    for i in range(d+1):
        t=F(i,d)
        M.append([comb(d,k)*t**k*(1-t)**(d-k) for k in range(d+1)]+[F(i==k) for k in range(d+1)])
    for i in range(d+1):
        p=next(j for j in range(i,d+1) if M[j][i]);M[p],M[i]=M[i],M[p]
        M[i]=[v/M[i][i] for v in M[i]]
        for j in range(d+1):
            if j!=i and M[j][i]:
                a=M[j][i];M[j]=[u-a*v for u,v in zip(M[j],M[i])]
    return [t[d+1:] for t in M]
def basis(dim,z,d):
    v=[F(1),z]
    if dim==1:return v
    for k in range(1,d):v.append(((2*k+dim-2)*z*v[k]-k*v[k-1])/(k+dim-2))
    return v
def mm(A,B):
    T=list(zip(*B))
    return [[sum((a*b for a,b in zip(row,col)),F()) for col in T] for row in A]
def split(v):
    d=len(v)-1;L=[];R=[]
    for i in range(d+1):
        L.append(v[0]<<(d-i));R.append(v[-1]<<(d-i));v=[a+b for a,b in zip(v,v[1:])]
    return L,R[::-1]
def tree(B,dep=0):
    if all(x>=0 for r in B for x in r):return 1
    assert dep<25 and max(x for r in B for x in r)>=0,('uncertified sign',dep)
    # split in y, alternating with x when x has positive degree
    flip=len(B)>1 and dep%2==1
    V=list(zip(*B)) if flip else B
    Z=[split(v) for v in V];L=[a for a,b in Z];R=[b for a,b in Z]
    if flip:L=list(zip(*L));R=list(zip(*R))
    return 1+tree(L,dep+1)+tree(R,dep+1)
def rectangles(r,w):
    if w==1:
        return [(F(-1),F(-1) if r==1 else F(1,2),F(1),F(1))]
    def top(x):return min(F(1),(F(1,2)-w*x)/(1-w))
    if r==1:
        return [(x,x,top(x),top(x)) for x in [F(-1),F(1)] if top(x)>=-1]
    cuts={F(-1),F(1)}
    if w:
        for v in [-1,1]:
            x=(F(1,2)-(1-w)*v)/w
            if -1<x<1:cuts.add(x)
    cs=sorted(cuts);return [(a,b,top(a),top(b)) for a,b in zip(cs,cs[1:]) if top((a+b)/2)>=-1]
def verify(r,a,b,L,chart):
    assert r in (1,2,3) and 0<=a<b<=2**L and chart
    D=10**7
    assert all(i>=0 and j>=0 and 0<i+j<=10 and (r!=1 or i<=1) and isinstance(c,int) and c>0 for i,j,c in chart)
    assert D+sum(c for i,j,c in chart)<127*D
    deg=max(i+j for i,j,c in chart);dy=max(j for i,j,c in chart);nodes=0
    for w in (F(a,2**L),F(b,2**L)):
        for u0,u1,v0,v1 in rectangles(r,w):
            dx=0 if u0==u1 else deg
            X=[]
            for k in range(dx+1):
                t=F(k,dx or 1);u=u0+t*(u1-u0);vmax=v0+t*(v1-v0);P=basis(r,u,deg)
                row=[]
                for j in range(dy+1):
                    v=F(-1)+F(j,dy or 1)*(vmax+1);T=basis(7-r,v,dy)
                    row.append(-D-sum(c*P[i]*T[h] for i,h,c in chart))
                X.append(row)
            Z=mm(mm(invbern(dx),X),list(zip(*invbern(dy))))
            den=lcm(*(v.denominator for row in Z for v in row))
            B=[[int(den*v) for v in row] for row in Z]
            nodes+=tree(B)
    return nodes
def check(rows):
    for r in [1,2,3]:
        spans=sorted((F(a,2**L),F(b,2**L)) for d,a,b,L,ch in rows if d==r)
        assert spans and spans[0][0]==0 and spans[-1][1]==1 and all(a[1]==b[0] for a,b in zip(spans,spans[1:]))
    nodes=0
    for row in rows:
        try:nodes+=verify(*row)
        except Exception as e:raise RuntimeError(('chart',row[:4])) from e
    print('Verified',len(rows),'closed radius intervals;',nodes,'Bernstein nodes.')
if __name__=='__main__':
    check(json.loads((Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('kissing-seven-product-sphere-charts.json')).read_text()))
