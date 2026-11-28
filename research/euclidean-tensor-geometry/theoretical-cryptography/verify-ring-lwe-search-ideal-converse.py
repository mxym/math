#!/usr/bin/env python3
"""Exact checks for the joint ideal converse, on generated synthetic spaces only."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import log

def mul(a,b,d):
    out=0
    for k in range(d):
        if (b>>k)&1:
            out ^= a<<k
    return out & ((1<<d)-1)

def subspaces(d):
    return [tuple(j for j in range(1<<d) if j% (1<<k)==0)
            for k in range(d+1)]

@lru_cache(None)
def image(row,J,d):
    hs={0}
    for a in row:
        hs={x^mul(a,y,d) for x in hs for y in J}
    return tuple(sorted(hs))

def prob(d,k):
    w=[1+((x+2)*(k+3)+x*x)%13 for x in range(1<<d)]
    return tuple(Q(a,sum(w)) for a in w)

@lru_cache(None)
def avg(p,H):
    return tuple(sum(p[x^h] for h in H)/len(H) for x in range(len(p)))

def signal(row,S,d):
    r=0
    for a,x in zip(row,S):
        r ^= mul(a,x,d)
    return r

def row_policy(hist,kind,d):
    B=1<<d
    if not hist:
        return (kind % B,(kind+2) % B)
    return ((hist[-1]^kind)%B,(hist[-1]+2*kind)%B)

nlik=ninv=0
for d in (2,3):
    D=1<<d
    for kind in range(5):
        p=prob(d,kind)
        for J in subspaces(d):
            if len(J)==1:
                continue
            for exact_H in (False,True):
                rs=defaultdict(dict)
                for s in product(range(D),repeat=2):
                    sid=tuple(min(x^j for j in J) for x in s)
                    for b1,b2 in product(range(D),repeat=2):
                        a1=row_policy((),kind,d)
                        a2=row_policy((b1,),kind,d)
                        h1,h2=tuple(image(a,J,d) if exact_H else J for a in (a1,a2))
                        p1,p2=avg(p,h1),avg(p,h2)
                        e1,e2=b1^signal(a1,s,d),b2^signal(a2,s,d)
                        true=p[e1]*p[e2]
                        ref=p1[e1]*p2[e2]
                        likelihood=p[e1]/p1[e1]*p[e2]/p2[e2]
                        assert true==likelihood*ref
                        nlik+=1
                        kk=(b1,b2)
                        if kk in rs[sid]:
                            assert ref==rs[sid][kk]
                            ninv+=1
                        rs[sid][kk]=ref

# Direct conditional-fiber multiplicative derivative and exact
# translation Fourier projection, in several nilpotent toy orders.
nf=nparse=0
for d in range(1,7):
    D=1<<d
    for zz in range(3):
        p=prob(d,zz)
        for J in subspaces(d):
            a=avg(p,J)
            energy=sum((x-y)**2 for x,y in zip(p,a))*D
            direct=Q(0)
            for w in range(D):
                chi=lambda x: (-1)**((w&x).bit_count()%2)
                P=sum(p[x]*chi(x) for x in range(D))
                A=sum(a[x]*chi(x) for x in range(D))
                if any(chi(j)==-1 for j in J):
                    assert A==0
                    direct+=P*P
                else:
                    assert A==P
                nf+=1
                assert p[w]/a[w]==len(J)*p[w]/sum(p[w^j] for j in J)
            assert direct==energy
            nparse+=1

# Validate the submodular identity for truly crossing subgroups
# in the finite additive product of two binary fields.
ncm=0
pairs=[(0,1),(0,2),(0,3)]
for a,b,c,d in product(range(1,5),repeat=4):
    P=tuple(Q(x,a+b+c+d) for x in (a,b,c,d))
    for H,J in product(pairs,repeat=2):
        W=tuple(sorted({x^y for x in H for y in J}))
        I=tuple(sorted(set(H)&set(J)))
        AH,AJ,AW,AI=tuple(avg(P,T) for T in (H,J,W,I))
        for x in range(4):
            pU=sum(P[x^u] for u in H)/sum(P[x^w] for w in W)
            pV=sum(P[x^v] for v in J)/sum(P[x^w] for w in W)
            pUV=sum(P[x^i] for i in I)/sum(P[x^w] for w in W)
            assert AI[x]*AW[x]/(AH[x]*AJ[x])==pUV/(pU*pV)
            ncm+=1

assert 3**3>2**4
def h(p):
    return -p*log(p)-(1-p)*log(1-p)
lo,hi=Q(2,3),Q(99,100)
assert h(float(lo))>float(lo)*log(2)
assert h(float(hi))<float(hi)*log(2)
for _ in range(24):
    m=(lo+hi)/2
    if h(float(m))>float(m)*log(2):
        lo=m
    else:
        hi=m
assert Q(2,3)<lo<hi<Q(99,100)
assert 2*(1-lo)<lo
print("PASS: adaptive change-of-measure rows and reference invariance =",nlik,ninv)
print("PASS: finite fiber multipliers and exact Fourier projections =",nf,nparse)
print("PASS: crossing-fiber conditional independence identities =",ncm)
print("Opposite-sign nested tie (non-certifying display bracket):",float(lo),float(hi))
