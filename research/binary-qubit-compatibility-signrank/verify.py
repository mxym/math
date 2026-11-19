#!/usr/bin/env python3
"""Exact rational test of the tensor flattening and zero sign convention, plus H certificate."""
from itertools import product,combinations_with_replacement
from fractions import Fraction as F
from functools import lru_cache
def ck(x,msg):
    if not x:raise ArithmeticError(msg)
G=(1,-1,-1,-1)
def ip(x,y):return sum(s*a*b for s,a,b in zip(G,x,y))
def cp(e):return (1-e[0],)+tuple(-x for x in e[1:])
def tr(T):return sum(G[k]*T[k][k] for k in range(4))
@lru_cache(None)
def make(e):
    p=cp(e); te=tuple(tuple((e[i]*p[j]+e[j]*p[i])/2 for j in range(4)) for i in range(4))
    ck(tr(te)==ip(e,p),'trace')
    ck(te[0][0]==e[0]*(1-e[0]),'linear shift')
    return p,te,ip(e,e)*ip(p,p)
def sgn(b,a):
    # Exact sign of b+sqrt(a), retaining zero when a=b^2, b<=0.
    ck(a>=0,'radicand')
    if b>0:return 1
    return (a>b*b)-(a<b*b)
effects=set()
for e0 in [F(k,4) for k in range(5)]:
    for t in (F(0),F(2,3),F(1)):
        r=min(e0,1-e0)*t
        for v in [(1,0,0),(0,1,0),(0,0,1),(F(3,5),F(-4,5),0),(F(2,3),F(2,3),F(-1,3))]:
            for sign in (-1,1):
                e=(e0,)+tuple(sign*r*x for x in v);p=cp(e)
                ck(ip(e,e)>=0 and ip(p,p)>=0,'non-effect')
                effects.add(e)
pairs=comm=sharp=ub=zeros=0
for e,f in combinations_with_replacement(sorted(effects),2):
    ep,T,rad=make(e);fp,S,rad2=make(f)
    b=ip(e,f)*ip(ep,fp)+ip(e,fp)*ip(ep,f)-ip(e,ep)*ip(f,fp)
    lb=2*sum(G[i]*G[j]*T[i][j]*S[i][j] for i in range(4) for j in range(4))-tr(T)*tr(S)
    ck(lb==b,'tensor factorization')
    sp=sgn(b,rad*rad2);pairs+=1;zeros+=sp==0
    com=all(e[i]*f[j]==e[j]*f[i] for i in (1,2,3) for j in (1,2,3))
    if com:
        comm+=1;ck(sp>=0,'commuting effects')
    if (ip(e,e)==ip(ep,ep)==0) or (ip(f,f)==ip(fp,fp)==0):
        sharp+=1;ck((sp>=0)==com,'sharp effect: commutation criterion')
    if e[0]==f[0]==F(1,2):
        a=[2*x for x in e[1:]];c=[2*x for x in f[1:]]
        z=sum(x*x for x in a)+sum(y*y for y in c)<=1+sum(x*y for x,y in zip(a,c))**2
        ub+=1;ck(z==(sp>=0),'independent unbiased pair criterion')
n=128;H=[[1-2*((x&y).bit_count()%2) for y in range(n)] for x in range(n)]
for x in range(n):
    for z in range(x,n):
        ck(sum(a*b for a,b in zip(H[x],H[z]))==n*(x==z),'Hadamard')
ck(128>11**2,'Forster gap')
print('effects=%s unordered_pairs_including_repeats=%s boundary_zeros=%s commuting=%s sharp=%s unbiased=%s'%(len(effects),pairs,zeros,comm,sharp,ub))
print('HH^T=128I: all 8256 upper triangular products checked; 128>121. Graph has 256 vertices; edges:',sum(x==1 for row in H for x in row))
