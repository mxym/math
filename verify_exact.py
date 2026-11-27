#!/usr/bin/env python3
"""Enumerate all small affine-hyperplane zero patterns via exact row spaces."""
from itertools import combinations, combinations_with_replacement
from math import gcd, comb


def elim(v,basis):
    v = list(v)
    for p,b in basis:
        if v[p]:
            a=v[p]
            v=[b[p]*x-a*y for x,y in zip(v,b)]
            g=gcd(*v)
            if g>1: v=[x//g for x in v]
    return tuple(v)


def echelon(rows):
    basis=[]
    for row in rows:
        v=elim(row,basis)
        j=next((j for j,a in enumerate(v) if a),None)
        if j is not None:
            basis.append((j,v))
            basis.sort()
    return basis


def all_zero_patterns(n):
    rows=[(1,)+tuple(x>>i&1 for i in range(n)) for x in range(1<<n)]
    result=[]
    for z in range(1<<len(rows)):
        b=echelon(row for x,row in enumerate(rows) if z>>x&1)
        if len(b)==n+1: continue
        # A nonzero linear functional vanishing on these rows must not
        # vanish on any others. This is feasible iff no outside row lies
        # in the same span (finite union of proper subspaces over Q).
        if all(any(elim(row,b)) for x,row in enumerate(rows) if not z>>x&1):
            result.append(z)
    return result


def relevant(n,z):
    return sum(1<<t for t in range(n) if any(((z>>x)^(z>>(x^(1<<t))))&1
                                           for x in range(1<<n)))


def cover(L,full):
    union=0
    for x in L: union|=x
    return union==full


def test_family(n,f,axes,full):
    inc=full
    for x in f: inc&=x
    if inc or not cover(f,full): return None
    indices=range(len(f))
    I=next(i for k in range(2,len(f)+1) for i in combinations(indices,k)
           if cover([f[j] for j in i],full))
    k=len(I)
    U=0
    for j in I: U|=axes[f[j]]
    xs=[a for a in range(n) if U>>a&1]
    assert len(xs)<={2:2,3:12,4:80}[k]
    assert all(sum((axes[f[j]]>>a)&1 for j in I)>=2 for a in xs)
    lookup={}
    for x in range(1<<n):
        z=x&U
        if z not in lookup:
            index=next((j for j in I if not f[j]>>x&1),None)
            if index is None:
                [index]=[j for j in indices if j not in I]
            lookup[z]=index
        assert not f[lookup[z]]>>x&1
    return k


def main():
    B=lambda x:comb(x,x//2)
    for k,L in ((2,2),(3,8),(4,40)):
        assert B(L)*2**(k-1)>=2**L
        assert B(L+1)*2**(k-1)<2**(L+1)
    print('exact central-binomial boundaries: minimal covers k=2,3,4 -> L=2,8,40')
    for n in range(1,4):
        universe=all_zero_patterns(n)
        X={z:relevant(n,z) for z in universe}
        full=(1<<(1<<n))-1
        counts=[0,0,0]
        totals=0
        for m in range(2,5):
            for f in combinations_with_replacement(universe,m):
                totals+=1
                k=test_family(n,f,X,full)
                if k: counts[k-2]+=1
        print(f'n={n}: {len(universe)} real-affine zero patterns, {totals} families; valid by minimal size {counts}')
    print('PASS exhaustive rank-defined small real-affine covers and localized selector')


if __name__=='__main__': main()
