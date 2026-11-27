#!/usr/bin/env python3
"""Finite exact sanity checks for the near-prime Brocard witness argument."""
from collections import Counter, defaultdict
from fractions import Fraction
from math import isqrt, factorial, gcd

def primes_to(top):
    p=bytearray(b'\1')*(top+1)
    p[0]=p[1]=0
    for a in range(2,isqrt(top)+1):
        if p[a]:
            p[a*a:top+1:a]=b'\0'*((top-a*a)//a+1)
    return [n for n in range(2,top+1) if p[n]]

def symbol(a,p):
    v=pow(a%p,(p-1)//2,p)
    assert v in (0,1,p-1)
    return -1 if v==p-1 else v

def vp(n,p):
    a=0
    while n%p==0:
        n//=p
        a+=1
    return a

def Az(r):
    a=factorial(r-1)
    b=a+(-1)**r
    assert b>0 and gcd(a,b)==1
    return a*b

def main():
    A={r:Az(r) for r in range(2,301)}
    assert A[2]==A[3]==2
    assert all(isqrt(a)**2!=a for a in A.values())
    unit=0
    for p in primes_to(1009)[1:]:
        fac=[1]*p
        for j in range(1,p):
            fac[j]=j*fac[j-1]%p
        for r in range(2,min(300,p-1)+1):
            assert fac[p-r]*fac[r-1]%p==(-1)**r%p
            assert symbol(fac[p-r]+1,p)==symbol(A[r],p)
            unit+=1
    val=0
    ps=primes_to(300)
    for r in range(5,301):
        for s in range(r+1,min(300,4*r//3)+1):
            for p in ps:
                if r<=2*p<=s-1:
                    assert list(range(((r+p-1)//p)*p,s,p))==[2*p]
                    assert p<=r-1 and vp(A[s],p)-vp(A[r],p)==1
                    val+=1
    P=primes_to(200074)
    overlap_checks=0
    for X,H in [(2000,16),(20000,24),(50000,32),(100000,72)]:
        count=Counter()
        by_shift=defaultdict(set)
        for p in P:
            if not X+2<p<=2*X+H:
                continue
            for r in range(max(2,p-2*X),min(H,p-X-1)+1):
                if symbol(A[r],p)==-1:
                    n=p-r
                    count[n]+=1
                    by_shift[r].add(n)
        assert len(set().union(*by_shift.values()))==len(count)
        assert sum(map(len,by_shift.values()))==sum(count.values())
        hits=sum(k*(k-1)//2 for k in count.values())
        direct=sum(len(by_shift[r]&by_shift[s]) for r in range(2,H+1) for s in range(r+1,H+1))
        assert direct==hits
        assert sum(count.values())-hits<=len(count)
        assert sum(k>1 for k in count.values())<=hits
        minima=[min(r for r in range(2,H+1) if n in by_shift[r]) for n in count]
        prefix=set()
        for k in range(2,H+1):
            prefix.update(by_shift[k])
            assert sum(r<=k for r in minima)==len(prefix)
            overlap_checks+=1
    # Euler-product identity behind the averaged overlap bound.
    singular_checks=0
    for h in range(1,301):
        fs=[p for p in ps if p>2 and h%p==0]
        a=Fraction(1)
        terms={1:Fraction(1)}
        for p in fs:
            a*=1+Fraction(1,p-2)
            terms.update({p*d:v/(p-2) for d,v in terms.items()})
        assert sum(terms.values())==a and all(h%d==0 for d in terms)
        singular_checks+=1
    print('Wilson identity and symbols:',unit)
    print('square-class separators:',val)
    print('exact minimum-offset CDF union checks:',overlap_checks)
    print('singular factor expansions:',singular_checks)

if __name__=='__main__':
    main()
