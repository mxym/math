#!/usr/bin/env python3
"""Exact checks for a posterior identity in synthetic finite probability laws."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from random import Random

def probs(xs):
    return [F(x,sum(xs)) for x in xs]

rng=Random(113)
tails=lists=identities=0
for n in range(2,11):
    for _ in range(90):
        ka,ky=3,5
        qi=probs([rng.randrange(1,30) for _ in range(ka)])
        Q=[probs([rng.randrange(1,25) for _ in range(ky)]) for _ in range(ka)]
        P=[[probs([rng.randrange(1,25) for _ in range(ky)]) for _ in range(n)] for _ in range(ka)]
        prior=probs([rng.randrange(1,30) for _ in range(n)])
        grp=[rng.randrange(1+n//2) for _ in range(n)]
        labels=set(grp)
        prior_f={z:sum(prior[s] for s in range(n) if grp[s]==z) for z in labels}
        C=max(sum(qi[A]*sum(P[A][s][y]*P[A][z][y]/Q[A][y] for y in range(ky))
                  for A in range(ka)) for s in range(n) for z in range(s))
        data=[]
        for A in range(ka):
            local=[]
            for y in range(ky):
                LS=[P[A][s][y]/Q[A][y] for s in range(n)]
                mix=sum(prior[s]*LS[s] for s in range(n))
                grouped={z:sum(prior[s]*LS[s] for s in range(n) if grp[s]==z) for z in labels}
                for s in range(n):
                    z=grp[s]
                    w=prior[s]*LS[s]
                    W=qi[A]*Q[A][y]*w
                    ds=mix/max(1,w)
                    dfcond=grouped[z]/prior_f[z]/max(1,w/prior_f[z])
                    posterior_f=grouped[z]/mix
                    proxy=max(prior_f[z],min(1,w))
                    df=proxy/posterior_f
                    assert df==ds/dfcond
                    assert ds<=1+mix-w
                    if w>=1:
                        assert ds>=1
                    else:
                        assert ds==mix
                    data.append((W,ds,df))
                    local.append((Q[A][y]*w, y, z,posterior_f))
                    identities+=1
            for L in range(1,len(labels)+1):
                best=F(0)
                for y in range(ky):
                    mass=Counter()
                    for W,u,z,p in local:
                        if u==y:
                            mass[z]+=W
                    best+=sum(sorted(mass.values(),reverse=True)[:L])
                for a in (F(1),F(3,2),F(2),F(5,2),F(4)):
                    lower=sum(W for W,_,_,p in local if p>=a/L)
                    upper=sum(W for W,_,_,p in local if p>=1/(a*L))+1/a
                    assert lower<=best<=upper
                    lists+=1
        assert sum(W for W,_,_ in data)==1
        for a in (F(1),F(3,2),F(2),F(5,2),F(4),F(10),F(32)):
            assert sum(W for W,r,_ in data if r>a or r<1/a)<=(2+C)/a
            assert sum(W for W,_,r in data if r>a*a or r<1/(a*a))<=2*(2+C)/a
            tails+=1

def mul(a,b,q):
    d=len(a); c=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r=i+j; c[r%d]+=(-1 if r>=d else 1)*x*y
    return tuple(x%q for x in c)
def plus(a,b,q):
    return tuple((x+y)%q for x,y in zip(a,b))
def dot(a,b,q):
    return sum(x*y for x,y in zip(a,b))%q
overlaps=0
for q in (3,5,9):
    R=list(product(range(q),repeat=2))
    for _ in range(18):
        d1,d2=rng.choice(R),rng.choice(R)
        vals=Counter(plus(mul(a,d1,q),mul(b,d2,q),q) for a,b in product(R,repeat=2))
        assert len(set(vals.values()))==1
        I=list(vals)
        direct=sum((F(3+q*(x==0),4)*F(3+q*(y==0),4) for x,y in I),F(0))/len(I)
        fft=sum((F(1,4)**sum(x!=0 for x in w) for w in R if all(dot(w,x,q)==0 for x in I)),F(0))
        assert direct==fft
        overlaps+=1
print("PASS true-value identities / list thresholds at fixed design / overlap-based tails / finite ring pairs:",
      identities,lists,tails,overlaps)


# Small synthetic phase-block sanity checks for the pair-tilted moment
# expansions.  This exercises the analytic centering, not the CLT or a search.
from math import cos,log,pi,prod
phase_blocks=0
for q,d,gen in ((3,4,(2,1,1,0)),(5,2,(2,1)),(9,2,(3,0))):
    I={mul(a,gen,q) for a in product(range(q),repeat=d)}
    assert len(I)>1
    M=q
    c=[cos(2*pi*j/M) for j in range(M)]
    B=list(product(range(M),repeat=d))
    for b in (1/32,1/64,1/128):
        rows={}
        for y in B:
            r=prod(1+2*b*c[a] for a in y)
            rows[y]=(r,log(r))
        norm=sx=sy=sxx=sxy=syy=0.0
        for y,(r,x) in rows.items():
            for v in I:
                p,z=rows[tuple((a-h)%q for a,h in zip(y,v))]
                w=r*p
                norm+=w; sx+=w*x; sy+=w*z
                sxx+=w*x*x; sxy+=w*x*z; syy+=w*z*z
        assert abs(norm/(len(B)*len(I))-1)<max(1e-12,200*b**6)
        ux,uy=sx/norm,sy/norm
        assert max(abs(u-d*b*b) for u in (ux,uy))<40*b**3
        assert max(abs(sxx/norm-ux*ux-2*d*b*b),
                   abs(syy/norm-uy*uy-2*d*b*b),
                   abs(sxy/norm-ux*uy))<80*b**3
        phase_blocks+=1
print("PASS synthetic pair-tilted phase-block moments:",phase_blocks)
