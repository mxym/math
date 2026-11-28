#!/usr/bin/env python3
"""Finite support, local-statistic, unit-repair and objective identities."""
from collections import Counter
from itertools import combinations, product
from random import Random
rng=Random(651)

slots=0
for q,J in [(3,0),(3,1),(3,3),(5,1),(5,2)]:
    N=4
    p=[(J+1)*i for i in range(N)]
    rows=[(i,j,u) for i,j in combinations(range(N),2)
          for u in range(1,q) for _ in range(q*(q-1))]
    d=1
    while d<=max(4*(2*J+1)*len(rows),2*p[-1]+2*J+2): d*=2
    blocked=set()
    placed=[]
    for i,j,u in rows:
        for t in range(d):
            a,b=(t-p[i])%d,(t-p[j])%d
            if a not in blocked and b not in blocked: break
        else: raise AssertionError("no support placement")
        assert J<min((a-b)%d,(b-a)%d)
        placed.extend((a,b))
        blocked.update((x+v)%d for x in (a,b) for v in range(-J,J+1))
        slots+=1
    assert len(set(placed))==2*len(rows)
    ps=sorted(placed)
    assert min((ps[(i+1)%len(ps)]-ps[i])%d for i in range(len(ps)))>J

def coeff(a,g,x,q):
    d=len(g)
    return sum(w*g[(x-p)%d]*(-1 if x<p else 1) for p,w in a)%q

q,d=3,8
rows=(((0,1),(2,2)),((4,1),(6,1)))
types=tuple(product(range(2),range(2)))
choices=[z for k in (1,2,3,4) for z in combinations(types,k)]
counts=[[Counter() for z in choices] for x in range(d)]
for g in product(range(q),repeat=d):
    for x in range(d):
        for k,z in enumerate(choices):
            r=tuple(coeff(rows[i],g,(x+o)%d,q) for i,o in z)
            counts[x][k][r]+=1
patterns=0
for x in range(d):
    for z,H in zip(choices,counts[x]):
        assert len(H)==q**len(z)
        assert set(H.values())=={q**(d-len(z))}
        patterns+=len(H)

def rtrim(a,q):
    a=[x%q for x in a]
    while a and not a[-1]: a.pop()
    return a
def remainder(a,b,q):
    a=rtrim(a,q);b=rtrim(b,q)
    inv=pow(b[-1],-1,q)
    while len(a)>=len(b):
        k=len(a)-len(b);w=inv*a[-1]%q
        for j,z in enumerate(b): a[k+j]=(a[k+j]-w*z)%q
        a=rtrim(a,q)
    return a
def unit(a,q):
    d=len(a);x=[1]+[0]*(d-1)+[1];y=list(a)
    y=rtrim(y,q)
    while y: x,y=y,remainder(x,y,q)
    return len(x)==1
def ring(a,b,q):
    d=len(a)
    return tuple(coeff([(p,w) for p,w in enumerate(a) if w],b,j,q) for j in range(d))
repair=group=0
for q in (3,5):
    for v in product(range(q),repeat=4):
        ws=[((v[0]+c)%q,)+v[1:] for c in range(q)]
        assert any(unit(w,q) for w in ws)
        repair+=1
    for _ in range(200):
        v=tuple(rng.randrange(q) for j in range(8))
        ws=[((v[0]+c)%q,)+v[1:] for c in range(q)]
        w=next(a for a in ws if unit(a,q))
        s=tuple(rng.randrange(q) for j in range(8))
        z=tuple(rng.randrange(q) for j in range(8))
        assert ring(ring(z,w,q),s,q)==ring(z,ring(w,s,q),q)
        group+=1

score=0
for q in (3,5,7,11):
    for _ in range(30):
        h=[100]+[0]*(q-1)
        for a in range(1,(q+1)//2): h[a]=h[-a]=rng.randrange(-5,9)
        H=sum(h)
        edge=lambda z: sum(q*h[(c-u*z)%q] for u in range(1,q) for c in range(1,q))
        for z in range(q):
            assert edge(z)-edge(0)==(q*(q*h[0]-H) if z else 0)
            no=sum((q-1)*h[(c-u*z)%q] for u in range(1,q) for c in range(q))
            assert no==(q-1)**2*H
            score+=1

print("PASS disjoint positions / local uniform counts / scalar unit repairs / gauge identities / score cases:",
      slots,patterns,repair,group,score)
