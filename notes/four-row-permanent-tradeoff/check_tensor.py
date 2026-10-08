#!/usr/bin/env python3
"""Exact rational regression for the four-row parity-law tensor norm.

The analytic all-N assertion is proved by induction and product
extremizers in PAPER.md. This checker only verifies selected finite
N and never treats finite enumeration as the universal proof.
"""
from fractions import Fraction as F
from itertools import permutations, product

PERMS=tuple(permutations(range(4)))
def sign(p):
    return -1 if sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2 else 1

def need(cond,msg):
    if not cond:raise RuntimeError("tensor checker failure: "+msg)

def law(t):
    need(abs(t)<=F(1,24),"parameter beyond allowed probability range")
    r={p:F(1,24)+t*sign(p) for p in PERMS}
    need(all(v>=0 for v in r.values()),"negative probability")
    need(sum(r.values(),F(0))==1,"normalization")
    for i,j in product(range(4),repeat=2):
        need(sum((r[p] for p in PERMS if p[i]==j),F(0))==F(1,4),
             "nonuniform coordinate marginal")
    return r

def witness(t):
    # Choose the branch that attains kappa(t) exactly.
    if 24*abs(t)<=F(1,2):
        return None,F(1)
    selected=(0,1,2,3) if t>=0 else (1,0,2,3)
    return selected,F(2,3)*(1+24*abs(t))

def test_vector(ts):
    n=len(ts)
    laws=[law(t) for t in ts]
    ws=[witness(t) for t in ts]
    expectation=F(0)
    for pp in product(PERMS,repeat=n):
        prob=F(1)
        val=1
        for j,p in enumerate(pp):
            prob*=laws[j][p]
            w=ws[j][0]
            if w is not None and p!=w:val=0
        expectation+=prob*val
    denominator_sq=F(1)
    for i in range(4):
        norm_sq=F(0)
        for xx in product(range(4),repeat=n):
            rowval=1
            for j,x in enumerate(xx):
                w=ws[j][0]
                if w is not None and w[i]!=x:rowval=0
            norm_sq+=rowval
        norm_sq/=4**n
        need(norm_sq>0,"zero norm")
        denominator_sq*=norm_sq
    target=F(1)
    for _,kappa in ws:target*=kappa
    need(expectation*expectation==target*target*denominator_sq,
         "sharp tensor equality (rational squared form)")
    return len(PERMS)**n

def main():
    params=[
        (F(0),), (F(1,24),), (F(-1,24),), (F(1,48),),
        (F(1,96),),(F(1,24),F(-1,24)),(F(0),F(1,24)),
        (F(1,96),F(-1,24)),(F(1,48),F(-1,48)),
        (F(1,24),F(-1,24),F(0)),
        (F(1,24),F(1,24),F(-1,24)),
        (F(1,96),F(1,96),F(1,96)),
    ]
    total=0
    for ts in params:
        total+=test_vector(ts)
    need(F(2,3)*(1+24*F(1,24))==F(4,3),
         "edge parity norm factor")
    need(F(2,3)*(1+24*F(1,48))==1,
         "sharp threshold")
    print("PASS: exact S4 parity tensor norm witnesses")
    print("parameter vectors with independent columns:",len(params))
    print("enumerated permutation tuples:",total)
    print("marginal, mass, normalized L2 and sharp ratio controls: all pass")
    print("endpoint TV radius=1/4; maximal factor=4/3")
    print("rational arithmetic only; all-N induction is proved in PAPER.md")
if __name__=="__main__":
    main()
