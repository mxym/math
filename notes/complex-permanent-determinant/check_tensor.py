#!/usr/bin/env python3
"""Exact finite replay of tensor-product extremal witnesses.

The manuscript proves the all-N tensor norm analytically. This verifier
independently enumerates S3^N for several rational t vectors and checks
the predicted lower witnesses, marginals, and norm ratios in Fraction
arithmetic. Finite enumeration is NOT used for the all-N theorem.
"""
from fractions import Fraction as F
from itertools import permutations, product

PERMS=list(permutations(range(3)))
def sign(pi):
    return -1 if sum(pi[i]>pi[j] for i in range(3) for j in range(i+1,3))%2 else 1

def need(cond,msg):
    if not cond:
        raise RuntimeError("tensor witness rejected: "+msg)

def law(t):
    need(abs(t)<=F(1,6),"invalid t")
    vals={pi:F(1,6)+t*sign(pi) for pi in PERMS}
    need(all(v>=0 for v in vals.values()),"probabilities")
    need(sum(vals.values(),F(0))==1,"total mass")
    for i,j in product(range(3),repeat=2):
        need(sum((val for pi,val in vals.items() if pi[i]==j),F(0))==F(1,3),
             "uniform marginals")
    return vals

def witness(t):
    sq=F(3,4)*(1+6*abs(t))**2
    if sq<=1:
        return None,F(1)
    target=(0,1,2) if t>=0 else (1,0,2)
    return target,sq

def f(w, i, x):
    return 1 if w is None or x==w[i] else 0

def certificate(ts):
    n=len(ts)
    laws=[law(t) for t in ts]
    ws=[witness(t) for t in ts]
    out=F(0)
    for pis in product(PERMS,repeat=n):
        prob=F(1)
        z=1
        for j,pi in enumerate(pis):
            prob*=laws[j][pi]
            for i in range(3):
                z*=f(ws[j][0],i,pi[i])
        out+=prob*z

    norms2=[]
    for i in range(3):
        mom=F(0)
        for xvec in product(range(3),repeat=n):
            value=1
            for j,x in enumerate(xvec):
                value*=f(ws[j][0],i,x)
            mom+=value*value
        norms2.append(mom/F(3**n))
    denom=F(1)
    for v in norms2:
        denom*=v
    need(denom>0,"nonzero normalized rows")
    ratio2=out*out/denom
    target=F(1)
    for _,sq in ws:
        target*=sq
    need(ratio2==target,"exact sharp tensor product lower witness")
    return len(PERMS)**n

def main():
    vectors=[
        (F(0),), (F(1,6),), (F(-1,6),), (F(1,24),),
        (F(1,10),F(-1,10)),(F(1,100),F(1,6)),
        (F(0),F(0),F(0)),
        (F(1,6),F(-1,6),F(1,24)),
        (F(1,10),F(-1,24),F(-1,6)),
        (F(1,100),F(1,24),F(1,10)),
    ]
    branches=0
    for ts in vectors:
        branches+=certificate(ts)
    # This deliberately altered claimed equality cannot hold.
    target,sq=witness(F(1,6))
    need(target is not None and sq != F(3,4)*F(3,2)**2,
         "corrupted extremal factor")
    print("PASS: exact normalized tensor lower witnesses for three-row laws")
    print("rational t-vectors checked:",len(vectors))
    print("total permutation-tuple cases:",branches)
    print("all one-point marginals and total masses checked")
    print("ratios squared equal products of sharp single-column factors")
    print("corrupted-factor negative control rejected")
    print("standard-library fractions only; no floating point or solver")

if __name__=="__main__":
    main()
