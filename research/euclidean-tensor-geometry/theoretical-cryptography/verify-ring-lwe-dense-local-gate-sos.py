#!/usr/bin/env python3
"""Exact toy checks of masked-shift read bounds and terminal-only provenance."""
from collections import Counter
from itertools import product
from random import Random

rng=Random(685)
def entries(d,sh,j):
    # Coefficient of s_j in scalar output sh of negacyclic multiplication.
    return (sh-j)%d,(1 if sh>=j else -1)

def proj_matrices(q,d,k,c,v):
    # v uses original coordinates ('s',j) and auxiliary masked shifts ('g',row,shift,mask).
    const=[0]*d
    T=[[0]*(k*d) for j in range(d)]
    for (i,sh),a in c.items():
        for j in range(d):
            u,g=entries(d,sh,j)
            T[j][i*d+u]-=g*a
    for tag,data,a in v:
        if tag=="s":
            const[data]+=a
        else:
            i,sh,S=data
            for j in S:
                u,g=entries(d,sh,j)
                T[j][i*d+u]+=g*a
    T=[[x%q for x in row] for row in T]
    return T,[x%q for x in const]

relations=truths=0
for q,d,k in ((2,3,2),(3,3,2),(4,2,2),(4,3,1),(6,3,1),(9,2,1)):
    root=list(product(range(k),range(d)))
    for _ in range(115):
        roots=rng.sample(root,rng.randrange(1,len(root)+1))
        c={r:rng.randrange(1,q) for r in roots}
        absent=rng.choice(roots)
        v=[]
        for __ in range(rng.randrange(5)):
            r=rng.choice(root)
            if r==absent or rng.randrange(2):
                v.append(("s",rng.randrange(d),rng.randrange(1,q)))
            else:
                mask=tuple(j for j in range(d) if rng.randrange(2))
                v.append(("g",(*r,mask),rng.randrange(1,q)))
        T,C=proj_matrices(q,d,k,c,v)
        R=len(c)+len(v)
        for j in range(d):
            u,si=entries(d,absent[1],j)
            assert T[j][absent[0]*d+u]==(-si*c[absent])%q!=0
        assert all(sum(T[j][mu]!=0 for j in range(d))<=R for mu in range(k*d))
        counts=[0]*d
        joint=0
        for x in product(range(q),repeat=k*d):
            checks=[(b+sum(a*z for a,z in zip(t,x)))%q==0 for t,b in zip(T,C)]
            for j,vv in enumerate(checks): counts[j]+=vv
            joint+=all(checks)
        assert all(2*m<=q**(d*k) for m in counts)
        assert 2**d * joint**R <= q**(d*k*R)
        relations+=1
        truths+=joint

# Exact projection of small arbitrary trees and linear gate provenance.
gates=0
for q in (2,3,4,6,9):
    for _ in range(300):
        d=8;k=2
        A=[[rng.randrange(q) for j in range(d)] for i in range(k)]
        orig=[tuple(int(x==j) for x in range(d)) for j in range(d)]
        P=orig[:]
        eq=[]
        pin=[]
        for i,sh in product(range(k),range(d)):
            ix=[]
            for j in range(d):
                u,sg=entries(d,sh,j)
                xx=tuple(z*A[i][u]*sg%q for z in orig[j])
                eq.append(({len(P):1,j:-A[i][u]*sg},None))
                ix.append(len(P)); P.append(xx)
            while len(ix)>1:
                a=ix.pop(rng.randrange(len(ix)))
                b=ix.pop(rng.randrange(len(ix)))
                eq.append(({len(P):1,a:-1,b:-1},None))
                pp=tuple((x+y)%q for x,y in zip(P[a],P[b]))
                ix.append(len(P)); P.append(pp)
            pos=ix[0]
            c=len(pin)
            pin.append(P[pos])
            eq.append(({pos:1},c))
        full=Counter()
        c=Counter()
        for vv,c0 in rng.sample(eq,18):
            z=rng.randrange(q)
            for i,a in vv.items(): full[i]+=z*a
            if c0 is not None: c[c0]+=z
        lhs=[sum(z*P[i][j] for i,z in full.items())%q for j in range(d)]
        rhs=[sum(z*pin[i][j] for i,z in c.items())%q for j in range(d)]
        assert lhs==rhs
        gates+=1
local=0
for q in (2,3,5,7):
    for a,t,c in product(range(q),repeat=3):
        feasible={(u+t*a)%q for u in range(q) if (u+t*a)%q==c}
        assert feasible=={c}
        assert [u for u in range(q) if (u+t*a)%q==c]==[(c-t*a)%q]
        local+=1
print("PASS unmatched-root read / exact finite solutions / projected gate provenance / local reverse constraints:",
      relations,truths,gates,local)
