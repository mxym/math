#!/usr/bin/env python3
"""Exact finite checks of orbit clipping, balanced sampling, and conditional acceptance."""
from fractions import Fraction as F
from itertools import product
from random import Random

rng=Random(1431)
def floor(x): return x.numerator//x.denominator
def clipped(L):
    n=len(L)
    C=[min(x,2) for x in L]
    a=sum(C)/n
    R=[x+(1-a)*(2-x)/(2-a) for x in C]
    assert 0<=a<=1 and sum(R)==n and all(0<=x<=2 for x in R)
    assert sum(abs(x-y) for x,y in zip(R,L))<=2*sum(max(0,x-2) for x in L)
    return R

def balanced(p):
    n=len(p)
    a=[F(0)]
    for x in p: a.append(a[-1]+x)
    assert a[-1]==F(n,2)
    cut=sorted(set([F(0),F(1)]+[x-floor(x) for x in a]))
    lottery=[]
    for l,r in zip(cut,cut[1:]):
        t=(l+r)/2
        chosen=[i for i in range(n) if floor(a[i+1]-t)>floor(a[i]-t)]
        assert len(chosen) in (n//2,(n+1)//2)
        lottery.append((r-l,set(chosen)))
    assert len(lottery)<=n+2 and sum(w for w,S in lottery)==1
    assert [sum(w for w,S in lottery if i in S) for i in range(n)]==p
    return lottery

repair=lotteries=emitted=0
for n in (3,5,9,15):
    for _ in range(35):
        c=rng.randrange(2,6)
        g0=[rng.randrange(1,7) for k in range(c)]
        g=[F(x,sum(g0)) for x in g0]
        H=[]
        for k in range(c):
            L=[0]*n
            L[rng.randrange(n)]=rng.randrange(20,80)
            for i in range(n): L[i]+=rng.randrange(0,7)
            L=[F(n*x,sum(L)) for x in L]
            H.append(clipped(L))
            repair+=1
        pp={}
        for k in range(c):
            for B in range(n):
                p=[H[k][(B-t)%n]/2 for t in range(n)]
                fam=balanced(p)
                pp[k,B]=[sum(w for w,S in fam if z in S) for z in range(n)]
                lotteries+=len(fam)
        # Directly average the public translate when a*s is a fixed location v.
        for v,k,Bb in product(range(n),range(c),range(n)):
            A=sum(g[k]*pp[k,(Bb+t)%n][(v+t)%n]/n**2 for t in range(n))
            assert A==g[k]*H[k][(Bb-v)%n]/(2*n)
            emitted+=1
        for v in range(n):
            assert sum(g[k]*H[k][(Bb-v)%n]/(2*n) for k,Bb in product(range(c),range(n)))==F(1,2)

replays=0
for _ in range(300):
    N=rng.randrange(5,60);T=rng.randrange(1,N+1)
    mode=[rng.randrange(1,101) for i in range(N)]
    sign=[rng.randrange(2) for i in range(N)]
    jitter=[rng.randrange(1009) for i in range(N)]
    past=None
    for j in range(rng.randrange(2,6)):
        ix=[i for i in range(N) if sign[i]][:T]
        emitted_rows=[(i,(mode[i]*211+jitter[i]*317)%1009) for i in ix]
        if past is not None: assert past==emitted_rows
        past=emitted_rows
        replays+=len(ix)

windows=0
for _ in range(100):
    N=rng.randrange(8,60)
    sign=[rng.randrange(2) for i in range(N)]
    rows=[rng.randrange(10**6) for i in range(N)]
    loc=[i for i in range(N) if sign[i]]
    if not loc: continue
    H=len(loc)
    B=rng.randrange(H)
    def eval_scan(buffered):
        high=-1; latent=-1; state=11
        seen=0; pending={}
        trace=[]
        for j in range(2*H):
            start=max(0,high-B)
            i=start+(state+123*j)%(H-start)
            high=max(high,i)
            if buffered:
                while seen<=high:
                    latent+=1
                    if sign[latent]:
                        pending[seen]=latent
                        pending.pop(seen-B-1,None)
                        seen+=1
                        assert len(pending)<=B+1
                k=pending[i]
            else:
                k=loc[i]
            state=(rows[k]+121*state+k+j)%100003
            trace.append((i,k,state))
        return trace
    x=eval_scan(False)
    assert x==eval_scan(True)
    windows+=len(x)

print("PASS orbit repairs / balanced intervals / translated accepted cells / immutable row replays / local accepted probes:",
      repair,lotteries,emitted,replays,windows)
