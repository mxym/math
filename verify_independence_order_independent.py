#!/usr/bin/env python3
"""Independent backward rank DP for the 14-vertex clique-valley audit.
The FFK upper bound is evaluated via the Turan-canonical expansion, not colex masks.
For each pair of strict-down and subsequent strict-up ranks, the backward DP tracks
the least feasible f_(k-1) for each fixed f_k. No shape flags are used.
Standard library only; run without -O.
"""
if not __debug__:raise RuntimeError("enable assertions")
from functools import lru_cache
from itertools import combinations_with_replacement,combinations
from math import comb
from heapq import heappush,heappop
def C(n,k):return comb(n,k) if 0<=k<=n else 0
def up(a,b):return -((-a)//b)
@lru_cache(None)
def tur(n,k,r):
    if k<0:return 0
    q,z=divmod(n,r)
    return sum(C(z,i)*(q+1)**i*C(r-z,k-i)*q**(k-i)for i in range(k+1))
@lru_cache(None)
def ff(a,k,r):
    if a==0 or r<k+1:return 0
    j=k
    while tur(j+1,k,r)<=a:j+=1
    b=a-tur(j,k,r)
    return tur(j,k+1,r)+(ff(b,k-1,r-1) if b else 0)
def tri(n,e):return max(0,up(4*e*e-n*n*e,3*n))if n else 0
def all_lower(n,r):
    lo={};q=n-r
    for S in combinations_with_replacement(range(r),q):
        freq=[S.count(j) for j in range(r)]
        costs=sorted(max(0,i+j-r)for i,j in combinations(S,2))
        cur=[C(r,j)+sum(freq[v]*C(v,j-1)for v in range(r))for j in range(r+1)]
        base=C(r,2)+sum(S)
        for e in range(1+len(costs)):
            m=base+e;y=cur[:];y[3]=max(tri(n,m),y[3]+tri(q,e));y[:3]=[1,n,m]
            if m not in lo:lo[m]=y
            else:lo[m]=list(map(min,lo[m],y))
            if e<len(costs):
                for j in range(3,r+1):cur[j]+=C(costs[e],j-2)
    return lo
def backward(n,r,m,lo,down,rise,force3=None):
    # Distinct strict steps indexed by their left rank.
    if (down==1 and n<=m) or (rise==1 and n>=m):return False
    hi=[1,n,m]
    for k in range(2,r):hi.append(ff(hi[-1],k,r))
    INF=10**8; beta={x:0 for x in range(lo[r],hi[r]+1)}
    for k in range(r-1,1,-1):
        nb={};pending=[];x0=lo[k+1];mx=-1
        for a in ([force3] if k==3 and force3 is not None else range(lo[k],hi[k]+1)):
            assert lo[k]<=a<=hi[k]
            bound=ff(a,k,r)
            if k==down:bound=min(bound,a-1)
            while x0<=bound:
                if x0 in beta:heappush(pending,(beta[x0],x0))
                x0+=1
            while pending and pending[0][0]<=a:mx=max(mx,heappop(pending)[1])
            if mx<lo[k+1] or (k==rise and mx<=a):continue
            nb[a]=up(k*k*a*a,(k*k-1)*mx+n*a)
        beta=nb
        if not beta:return False
    return beta.get(m,INF)<=n
n=14;masters=[]
for r in range(3,15):
    lo=all_lower(n,r)
    hits=[]
    for m in range(C(r,2),tur(n,2,r)+1):
        for down,rise in combinations(range(1,r),2):
            if backward(n,r,m,lo[m],down,rise):
                hits.append((m,down,rise))
    print('r',r,'hits',hits,flush=True);masters.extend((r,*v) for v in hits)
assert masters==[(7,50,2,3),(7,51,2,3)],masters
for _,m,down,rise in masters:
    # The unrestricted backward test at fixed degree-three value
    # leaves exactly one possibility; use brute-force f3/f4 interval.
    lo=all_lower(n,7)[m]
    eligible=[a for a in range(lo[3],min(m,ff(m,2,7)+1)) if a>=up(4*m*m-n*n*m,3*n) and ff(a,3,7)>a and backward(n,7,m,lo,down,rise,a)]
    assert eligible==[m-1],(m,eligible)
    ds=[]
    for D in combinations_with_replacement(range(7),7):
        e=m-21-sum(D);T=sum(C(v,2)for v in D);V=sum(C(v,3)for v in D)
        if 0<=e<=21 and T+tri(7,e)<=m-36:
            ds.append((D,35+V+4*(m-36-T)-3*tri(7,e)))
    print(m,'types',len(ds),'maximum',max(x for D,x in ds),ds,flush=True)
    assert (len(ds),max(x for D,x in ds))==((7,43) if m==50 else (2,40))
print('PASS')
