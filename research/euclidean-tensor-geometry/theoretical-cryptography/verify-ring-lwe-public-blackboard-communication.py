#!/usr/bin/env python3
"""Synthetic finite interactive transcript and non-label-dependent repair checks."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import sqrt
from random import Random
rng=Random(172)

def h2(P,Q): return sum((sqrt(float(a))-sqrt(float(b)))**2 for a,b in zip(P,Q))
def tv(P,Q): return sum(abs(float(a-b)) for a,b in zip(P,Q))/2

branches=steps=stops=0
for trial in range(220):
    n=3; ar=4; labels=3; total=5
    xspace=list(product(range(ar),repeat=n))
    prior=[F(1,labels)]*labels
    E=[]
    for i in range(n):
        rows=[]
        for s in range(labels):
            w=[rng.randrange(0,9) for a in range(ar)]
            if not any(w): w[0]=1
            rows.append([F(a,sum(w)) for a in w])
        E.append(rows)
    Qx=[[sum(prior[s]*E[i][s][u] for s in range(labels)) for u in range(ar)] for i in range(n)]
    def probs(s,x):
        ans=F(1)
        for i in range(n): ans*=(Qx[i][x[i]] if s is None else E[i][s][x[i]])
        return ans
    def sender(ts):
        return (len(ts)+sum(ts)+trial)%n
    def leaves(x):
        ts=()
        for t in range(total):
            i=sender(ts)
            bit=((x[i]+3*i+5*t+sum((j+1)*a for j,a in enumerate(ts))+trial)%5)<2
            ts+=int(bit),
        return ts
    paths={x:leaves(x) for x in xspace}
    qs=[defaultdict(F) for r in range(total+1)]
    ps=[[defaultdict(F) for r in range(total+1)] for s in range(labels)]
    for x,path in paths.items():
        for r in range(total+1):
            ts=path[:r]
            qs[r][ts]+=probs(None,x)
            for s in range(labels): ps[s][r][ts]+=probs(s,x)
    E0=0.
    for r in range(total):
        for ts,q in qs[r].items():
            if not q: continue
            bc=[qs[r+1][ts+(j,)]/q for j in range(2)]
            for s in range(labels):
                p=ps[s][r][ts]
                if p:
                    ac=[ps[s][r+1][ts+(j,)]/p for j in range(2)]
                    local=h2(ac,bc)
                    child_h2=h2([ps[s][r+1][ts+(j,)] for j in range(2)],
                                [qs[r+1][ts+(j,)] for j in range(2)])
                    assert float(q)*local<=4*child_h2+1e-12
                    E0+=float(prior[s]*q)*local
                steps+=1
    # Compute an exact finite version of the local event bound with a=1.
    ls=[]
    for i in range(n):
        limit=F(0)
        for mask in range(1,1<<ar):
            es=[u for u in range(ar) if mask>>u&1]
            den=sum(Qx[i][u] for u in es)
            if den:
                M=sum(prior[s]*(sum(E[i][s][u] for u in es)-den)**2 for s in range(labels))
                limit=max(limit,M/den)
        ls.append(limit)
    ms=[max(sum(sender(t[:j])==i for j in range(total)) for t in paths.values()) for i in range(n)]
    assert E0<=8*float(sum((2**m-1)*l for m,l in zip(ms,ls)))+1e-11
    base=[]; real=[]; repaired=[]
    stopped_real=stopped_modified=F(0)
    for s in range(labels):
        for leaf,q0 in qs[total].items():
            if not q0: continue
            old=ps[s][total][leaf]
            final=old
            for r in range(1,total+1):
                t=leaf[:r]
                N,D=ps[s][r][t],qs[r][t]
                if N>2*D:
                    final=q0*N/D
                    stopped_real+=prior[s]*old
                    stopped_modified+=prior[s]*final
                    stops+=1
                    break
            real.append(prior[s]*old)
            base.append(prior[s]*q0)
            repaired.append(prior[s]*final)
            branches+=1
    assert stopped_real==stopped_modified
    assert sum(base)==sum(real)==sum(repaired)==1
    assert h2(repaired,base)<=sqrt(2)*E0+1e-10
    assert tv(real,repaired)<=float(stopped_real)+1e-12
    assert tv(real,base)<=12*sqrt(2)*E0+2**.25*sqrt(E0)+1e-10

repairs=0
for _ in range(400):
    n=5; labels=3
    L=[]; U=[]
    for s in range(labels):
        w=[rng.randrange(1,10) for i in range(n)]
        p=[F(n*x,sum(w)) for x in w]
        L.append(p)
        U.append([F(4,5)*x for x in p])
    bar=[sum(U[s][i] for s in range(labels))/labels for i in range(n)]
    H=[max(0,1-x) for x in bar]
    den=sum(x+h for x,h in zip(bar,H))/n
    assert 1<=den<=2
    new=[[(x+h)/den for x,h in zip(row,H)] for row in U]
    mean=[sum(new[s][i] for s in range(labels))/labels for i in range(n)]
    assert min(mean)>=F(1,2)
    for s in range(labels):
        assert sum(new[s])==n
        assert all(new[s][i]-mean[i]==(U[s][i]-bar[i])/den for i in range(n))
        assert sum(abs(a-b) for a,b in zip(new[s],L[s]))/n<=2*(F(1,5)+sum(H)/n)
        repairs+=1

print("PASS synthetic transcript leaves / local prefixes / declared stops / shared repairs:",
      branches,steps,stops,repairs)
