#!/usr/bin/env python3
"""Enumerate inverse-survival identities for finite adaptive oracle trees."""
from fractions import Fraction as F
from itertools import combinations,product
from math import prod
from random import Random


def run(tree,H,blocked):
    path = []
    while isinstance(tree,tuple):
        addr,*edges=tree
        if addr in blocked:
            return None, addr, tuple(path)
        path.append(addr)
        tree=edges[H[addr]]
    return tree,None,tuple(path)


def subsets(S):
    return [frozenset(T) for n in range(len(S)+1)
            for T in combinations(S,n)]


def evaluate(H,tables,R,depth):
    ps=F(1,2*depth+2)
    masks=[(T,ps**len(T)*(1-ps)**(len(R)-len(T))) for T in subsets(sorted(R))]
    states=0
    wrong=0
    sq_sample=0
    for b,u,y in product((0,1),sorted(R),range(len(tables))):
        direct,stop,_=run(tables[y],H,{u})
        if stop==u: direct=b
        good,unweighted=F(0),F(0)
        for T,mass in masks:
            if u not in T: continue
            result,stop,path=run(tables[y],H,T)
            if stop==u: result=b
            if stop is not None and stop!=u: result=0
            assert result in (0,1)
            # Missing cells are never read. This includes the actual u.
            assert not set(path).intersection(T)
            good += mass*result/(1-ps)**len(R.intersection(path))
            unweighted += mass*result
        assert good==ps*direct
        if unweighted!=ps*direct: wrong+=1
        states+=1
    # Evaluate both sides of the centered identity independently of the
    # one-challenge coefficient assertions above.
    for b in (0,1):
        center=F(0)
        for u in R:
            vals=[(b if stop==u else d) for d,stop,path in
                  (run(tree,H,{u}) for tree in tables)]
            center+=vals[H[u]]-F(sum(vals),len(vals))
        mix=F(0)
        for T,mass in masks:
            for u in T:
                vals=[]
                for tree in tables:
                    d,stop,path=run(tree,H,T)
                    if stop==u: d=b
                    elif stop is not None: d=0
                    vals.append(F(d)/(1-ps)**len(R.intersection(path)))
                mix+=mass*(vals[H[u]]-sum(vals)/len(vals))/ps
        assert center==mix and abs(center)<=len(R)
        sq_sample+=center*center
    return states,wrong,sq_sample


def trees(cells,M,depth):
    current=(0,1)
    for j in range(depth):
        current=(0,1)+tuple((u,*children) for u in cells
                            for children in product(current,repeat=M))
    return current


def main():
    totals=0
    wrongs=0
    # Every pair of depth <=2 binary trees on two addresses. A separate
    # fixture below checks the full four-cell domain, outside cells and M=3.
    ts=trees(range(2),2,2)
    Hs=list(product(range(2),repeat=2))
    ps=F(1,6)
    for tables in product(ts,repeat=2):
        ss=0
        for H in Hs:
            a,b,s=evaluate(H,tables,frozenset((0,1)),2)
            totals+=a; wrongs+=b; ss+=s
        assert ss/len(Hs)<=2*F(2,1)/ps
    rng=Random(6020010)
    checks=0
    for M,depth,rid in product((2,3),(0,1,3),range(2)):
        R=(frozenset((0,1,2,3)) if rid==0 else frozenset((1,3)))
        def build(k):
            if k==0 or rng.randrange(5)==0: return rng.randrange(2)
            return (rng.randrange(4),*(build(k-1) for _ in range(M)))
        for _ in range(2):
            tables=tuple(build(depth) for _ in range(M))
            ss=0
            for H in product(range(M),repeat=4):
                a,b,s=evaluate(H,tables,R,depth)
                totals+=a; wrongs+=b; ss+=s; checks+=1
            assert ss/(M**4)<=2*len(R)*2*(depth+1)
    assert wrongs>0
    print(f"exact PASS: {totals} inverse-survival coefficients and centered identities ({checks} additional full-table fixtures)")
    print(f"exact PASS: {wrongs} unweighted-restriction failures detected; binary and ternary challenges; early stop and repeated queries")


if __name__=="__main__":
    main()
