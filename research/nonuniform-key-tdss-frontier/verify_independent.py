#!/usr/bin/env python3
"""Ground truth by exhaustive integer component vectors and decoder partitions."""
from functools import cache
from fractions import Fraction
from itertools import combinations,product
from math import comb

def analytic_budget(n,p):
    # Determine least Lorenz majorant from all supporting chords,
    # rather than clipping or decomposing the light-key law.
    T=sum(p)
    P=[0]
    for x in sorted(p,reverse=True):
        P.append(P[-1]+x)
    P += [T]*max(0,n+1-len(P))
    C=[Fraction(0)]
    for j in range(1,n+1):
        C.append(max(Fraction(P[j]),
                  *(Fraction((n-j)*P[i]+(j-i)*T,n-i) for i in range(j))))
    W=[b-a for a,b in zip(C,C[1:])]
    assert sum(W)==T and all(a>=b for a,b in zip(W,W[1:]))
    s=n//2
    return sum(max(0,2*sum(W[i] for i in A)-T)
               for A in combinations(range(n),s))

def grid(n,total):
    # A column-unique component uses an arbitrary submass of every key
    # and sends each nonzero column to one cell. A symmetry orbit uniformly
    # relabels those cells, preserving the average half-predicate objective.
    # Search all partitions of the given integer key masses into components.
    half=n//2
    A=list(combinations(range(n),half))
    @cache
    def local(p):
        p=tuple(x for x in p if x)
        lo=None
        mass=sum(p)
        for f in product(range(n),repeat=len(p)):
            v=[0]*n
            for i,x in zip(f,p):
                v[i]+=x
            d=sum(max(0,2*sum(v[j] for j in a)-mass) for a in A)
            lo=d if lo is None else min(lo,d)
            if lo==0: return lo
        return lo
    @cache
    def search(p):
        if not p: return 0
        lo=local(p)
        if lo==0: return lo
        # One summand must use some mass of the first positive key.
        for q in product(range(1,p[0]+1),*(range(x+1) for x in p[1:])):
            if q==p: continue
            r=tuple(sorted((a-b for a,b in zip(p,q) if a>b),reverse=True))
            t=tuple(sorted((x for x in q if x),reverse=True))
            lo=min(lo,local(t)+search(r))
            if lo==0: return lo
        return lo
    return search(tuple(sorted(total,reverse=True)))

def partitions(s, cap, maxlen):
    if not s:
        yield ()
    elif maxlen:
        for x in range(min(s,cap),0,-1):
            for tail in partitions(s-x,x,maxlen-1):
                yield (x,)+tail

tests=equal=strict=0
for n in range(2,5):
    for den in range(1,8):
        for p in partitions(den,den,5):
            opt=grid(n,p)
            lb=analytic_budget(n,p)
            assert opt>=lb,(n,p,opt,lb)
            equal+=opt==lb
            strict+=opt>lb
            tests+=1
# Integer granularity obstruction: grid size 3 cannot split the odd
# number of equal units into light-key pairs; size 6 makes all three pairs.
small=Fraction(grid(2,(1,1,1)),3*comb(2,1))
large=Fraction(grid(2,(2,2,2)),6*comb(2,1))
assert small==Fraction(1,6) and large==0
assert analytic_budget(2,(1,1,1))==0
assert equal>0 and strict>0
# The genuine short-key profile remains optimal already on integer grid,
# including one-key and very skew distributions.
for n,p in [(2,(1,)),(3,(6,1)),(4,(4,3,2,1))]:
    assert grid(n,p)==analytic_budget(n,p)
print(f"Exhaustive column-unique integer grid: {tests} pairs, "
      f"{equal} exact attainments, {strict} strict granularity gaps.")
print("Independent grid control: denominator 3 gives 1/6; denominator 6 gives 0.")
