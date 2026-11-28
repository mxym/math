#!/usr/bin/env python3
"""Exact primitive-direction and layout checks on small cyclic graphs."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd, isqrt, prod


def primes(n):
    out=[]
    j=2
    while j*j<=n:
        if n%j==0:
            out.append(j)
            while n%j==0:
                n//=j
        j+=1
    if n>1:
        out.append(n)
    return out


def jordan(n,k):
    return prod((p-1) if k==1 else (p**k-1)
                for p in primes(n))*(n//prod(primes(n)))**k


def divs(n):
    return [j for j in range(1,n+1) if n%j==0]


def units_in_first(n,t):
    # Number of residues x with gcd(x,n/t)=1, via an independent gcd loop.
    return sum(gcd(x,n//t)==1 for x in range(n))


@lru_cache(None)
def canonical_primitives(s,B):
    return tuple(v for v in product(range(-B,B+1),repeat=s)
                 if gcd(*v)==1 and next(x for x in v if x)>0)


def displacement(table,a):
    return min(max(row[x] for x in a) for row in table)


def transverse_order(n,a,v):
    return n//gcd(n,*(a[i]*v[j]-a[j]*v[i]
                       for i in range(len(a)) for j in range(i+1,len(a))))


def res(n,x):
    r=x%n
    return min(r,n-r)


def layout_check(n,a,k,table):
    witness=next(r for r,row in enumerate(table,1) if max(row[x] for x in a)==k)
    d=gcd(n,witness)
    h=n//d
    r=witness//d
    layers=[[] for _ in range(h)]
    for x in range(n):
        layers[r*x%h].append(x)
    assert all(len(layer)==d for layer in layers)
    order=[0]+[x for j in range(1,h//2+1)
                 for x in ((j,h-j) if 2*j!=h else (j,))]
    assert sorted(order)==list(range(h))
    pos=[0]*n
    for j,x in enumerate(y for i in order for y in layers[i]):
        pos[x]=j
    assert max(abs(pos[x]-pos[(x+y)%n]) for x in range(n) for y in a)+1<=3*k


def check_counts(n,s,extra):
    table=tuple(tuple(res(n,r*x) for x in range(n)) for r in range(1,n))
    Bmax=isqrt((n-1)//2)
    patterns=canonical_primitives(s,Bmax)
    law=Counter()
    seen=0
    nlayout=0
    npoint=0
    nfinite=0
    nprime=0
    for a in product(range(n),repeat=s):
        if gcd(n,*a)!=1:
            continue
        seen+=1
        k=displacement(table,a)
        law[k]+=1
        if seen%extra==1 or extra==1:
            layout_check(n,a,k,table)
            nlayout+=1
        if k<=Bmax or (seen%extra==1):
            ans=[transverse_order(n,a,v)*max(map(abs,v)) for v in patterns]
            good=[y for y in ans if y<=Bmax]
            assert len(good)==(k<=Bmax)
            if good:
                assert good[0]==k
            npoint+=1
    assert seen==jordan(n,s)
    P={b:len(canonical_primitives(s,b)) for b in range(1,Bmax+1)}
    for B in range(1,Bmax+1):
        actual=sum(v for k,v in law.items() if k<=B)
        expected=sum(jordan(t,s-1)*P[B//t]*units_in_first(n,t)
                     for t in divs(n) if t<=B)
        assert expected==actual
        nfinite+=1
        ps=primes(n)
        if len(ps)==1:
            p=ps[0]
            ssum=0
            for v in canonical_primitives(s,B):
                radius=max(map(abs,v))
                f=1
                while f*p*radius<=B:
                    f*=p
                ssum+=f**(s-1)
            rhs=Fraction((p-1)*p**(s-1)*ssum,(p**s-1)*n**(s-1))
            assert rhs==Fraction(actual,seen)
            nprime+=1
    return nlayout,npoint,nfinite,nprime


def weight_checks():
    k=0
    for n in range(2,301):
        for s in (2,3,4,5):
            value=sum(Fraction(jordan(t,s-1)*units_in_first(n,t),n*t**s)
                      for t in divs(n))
            assert value==Fraction(jordan(n,s),n**s)
            k+=1
    return k


def boundary_checks():
    count=0
    for B in range(2,46):
        n=B**2+(B-1)**2
        v=(B,B-1)
        w=(1-B,B)
        assert gcd(n,*v)==1 and gcd(*v)==1 and gcd(*w)==1
        assert transverse_order(n,v,v)==transverse_order(n,v,w)==1
        assert max(map(abs,v))==max(map(abs,w))==B
        count+=1
    for e in range(4,14):
        n=1<<e
        a=(1,n//2+1)
        assert max(res(n,2*x) for x in a)==2
        assert min(max(res(n,r*x) for x in a) for r in range(1,n,2))>2
        count+=1
    return count


def main():
    totals=[0]*4
    for n,s in [(n,2) for n in range(3,48)]+[
            (64,2),(72,2),(84,2),(96,2),(105,2),(128,2),
            (5,3),(8,3),(9,3),(12,3),(16,3),(20,3),(24,3),(27,3),(32,3),
            (5,4),(8,4),(9,4),(12,4)]:
        result=check_counts(n,s,19)
        totals=[x+y for x,y in zip(totals,result)]
    print("PASS layout / pointwise / divisor counts / prime powers / weights / boundary:",
          *totals,weight_checks(),boundary_checks())


if __name__=="__main__":
    main()
