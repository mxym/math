#!/usr/bin/env python3
"""Exact multibin witnesses and a separate direct binary-affine rank audit."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod


def falling(n, k):
    return prod(n-i for i in range(k))


def moments(ds):
    assert sum(ds) == 0
    return sum(d*d for d in ds), sum(d**3 for d in ds), sum(max(d,0) for d in ds)


def make_law(m,b,mode):
    N=m*b
    sym=(b,-b)*(m//2)+(0,)*(m%2)
    V0=b*(m-1)
    Vs,_,_=moments(sym)
    w=F(m-2,m)
    if mode=="universal":
        other=((m-1)*b,)+(-b,)*(m-1)
        po=F(1,N*N)
        ps=F(N-1,N)*F(V0,Vs)
    elif mode=="equality":
        stride=2*b+1
        other=((b+1,)*b+(-b,)*(b+1))*(m//stride)+(0,)*(m%stride)
        po=w*F(V0,moments(other)[0])
        ps=(1-w)*F(V0,Vs)
    else:
        assert m in (3,4)
        other=(2*b,-b,-b)+(0,)*(m-3)
        po=w*F(V0,b*moments(other)[0])
        ps=(1-w/b)*F(V0,Vs)
    return ((ps,sym),(po,other),(1-po-ps,(0,)*m))


def check_law(m,b,mode):
    N=m*b;w=F(m-2,m);law=make_law(m,b,mode)
    assert all(p>=0 and len(ds)==m and min(ds)>=-b for p,ds in law)
    assert sum(p for p,_ in law)==1
    # Check the factorial moments directly, not just centered expansions.
    for j in (2,3):
        target=F(falling(N,j),m**(j-1))
        assert sum(p*sum(falling(b+d,j) for d in ds) for p,ds in law)==target
    ans=sum(p*F(sum(abs(d) for d in ds),2*N) for p,ds in law)
    if mode=="universal":
        assert ans==F(m-1,2*N)*(1-w/N)
    elif mode=="equality":
        assert ans==F(m-1,2*N)*(1-w/(2*b+1))
    else:
        assert ans==F(m-1,2*N)*(1-w/(3*b))
    return ans


grid=[(m,b) for m in range(2,27) for b in range(1,35)]
eq=small=0
for m,b in grid:
    check_law(m,b,"universal")
    if m>=2*b+1:
        check_law(m,b,"equality")
        eq+=1
    if m in (3,4):
        check_law(m,b,"small")
        small+=1
print(f"Profile laws: {len(grid)} universal, {eq} integer-facet attainments, {small} m=3/4 exact cases")


def partitions(total,length,cap):
    if not length:
        if total==0:
            yield ()
        return
    for first in range(min(total,cap), (total+length-1)//length-1,-1):
        for tail in partitions(total-first,length-1,first):
            yield (first,)+tail


profiles=0
for m,b in product(range(2,8),range(1,7)):
    for cs in partitions(m*b,m,m*b):
        ds=tuple(x-b for x in cs)
        V,W,L=moments(ds)
        assert (2*b+1)*(V-2*b*L)<=W
        if m<=4:
            assert 3*b*(V-2*b*L)<=W
        profiles+=1
V,W,L=moments((3,3,-2,-2,-2))
assert 3*2*(V-2*2*L)>W
print(f"Pointwise bounds: {profiles} sorted profiles; m=5 negative control for the m<=4 facet")


def direct_output_law(m,b,mode):
    N=m*b
    for j in range(1,min(3,N)+1):
        out=Counter()
        for p,ds in make_law(m,b,mode):
            for perm in permutations(range(m)):
                counts=[b+ds[i] for i in perm]
                for labels in product(range(m),repeat=j):
                    mult=Counter(labels)
                    numer=prod(falling(counts[i],k) for i,k in mult.items())
                    out[labels]+=F(numer,falling(N,j))*p/falling(m,m)
        assert all(v==F(1,m**j) for v in out.values())
        assert len(out)==m**j


cases=[(2,1,"universal"),(2,4,"universal"),(3,2,"small"),
       (4,3,"small"),(5,2,"equality"),(6,2,"universal")]
for m,b,mode in cases:
    direct_output_law(m,b,mode)
    print(f"All labeled tuples through order three: N={m*b} m={m} law={mode} TV={check_law(m,b,mode)}")


def span(columns):
    S={0}
    for c in columns:
        S|={s^c for s in S}
    return S


def rank_count(d,r,j):
    val=F(1)
    for i in range(j):
        val*=F((2**d-2**i)*(2**r-2**i),2**j-2**i)
    assert val.denominator==1
    return val.numerator


rank_cases=0
for d in range(1,6):
    for r in range(1,min(d,3)+1):
        h=Counter(len(span(cs)).bit_length()-1 for cs in product(range(2**r),repeat=d))
        assert all(h[j]==rank_count(d,r,j) for j in range(r+1))
        assert sum(h.values())==2**(r*d)
        defect=1-F(h[r],2**(r*d))
        assert F(2**(r-1),2**d)<=defect<F(2**r,2**d)
        tv=sum(F(h[j],2**(r*d))*(1-F(2**j,2**r)) for j in range(r+1))
        assert defect/2<=tv<=defect
        rank_cases+=1
        if (d,r)==(3,2):
            print(f"Binary affine 3->2 rank histogram: {dict(sorted(h.items()))}; mean TV={tv}")

def aff(cs,c,x):
    for i,v in enumerate(cs):
        if x>>i&1:
            c^=v
    return c

maps=[tuple(aff(cs,c,x) for x in range(8))
      for cs in product(range(4),repeat=3) for c in range(4)]
for xs in combinations(range(8),3):
    h=Counter(tuple(row[x] for x in xs) for row in maps)
    assert len(h)==64 and set(h.values())=={4}
print(f"Binary affine: {rank_cases} exact rank cases and all 56 triples for 256 seeds")
