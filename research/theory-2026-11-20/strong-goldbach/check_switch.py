"""Integer-only finite tests of the divisor regrouping, triangular endpoints and square classes.

An additive expression in logs of positive rationals is zero iff its prime-valuation
vector is zero. This checks exact identities, not the distribution conjectures.
"""
from collections import Counter
from functools import cache
from math import gcd, isqrt, lcm

@cache
def factors(n):
    v, p = Counter(), 2
    while p*p <= n:
        while n % p == 0:
            v[p] += 1
            n //= p
        p += 1
    if n > 1:
        v[n] += 1
    return v

@cache
def mu(n):
    v = factors(n).values()
    return 0 if any(e > 1 for e in v) else (-1)**len(v)

@cache
def divisors(m):
    return tuple(d for a in range(1,isqrt(m)+1) if m%a==0
                 for d in ((a,) if a*a==m else (a,m//a)))

def add(v, t, a, b):
    for p,e in factors(a).items(): v[p] += t*e
    for p,e in factors(b).items(): v[p] -= t*e

def same(v, w): return all(v[k]==w[k] for k in v.keys()|w.keys())

cases = terms = zero_classes = 0
for m in range(2,1501):
    ds=divisors(m)
    for alpha in (2,5,17,64):
        S, small, large, rep, switch=Counter(),Counter(),Counter(),Counter(),Counter()
        for d in ds:
            add(S,mu(d),alpha,d)
            add(small if d<=alpha else large, mu(m)**2*mu(d),alpha,d)
            if d<=alpha and mu(d):
                for b in ds:
                    if m%(b*b) or not mu(b): continue
                    g=gcd(b,d); h=d//g; z=b*b*h
                    assert g in divisors(b) and gcd(b,h)==1 and z==lcm(b*b,d)
                    assert m%z==0
                    add(rep,mu(b)*mu(g)*mu(h),alpha,g*h)
                    for B in (2,3):
                        if z>alpha*B*B:
                            assert b>B and g*B*B<=b*b and alpha*B*B<h*b*b and g*h<=alpha
                            assert alpha*B*B<=g*h*b*b
                    terms+=1
        for k in ds:
            if alpha*k<m: add(switch,mu(m)*mu(k),alpha*k,m)
        expected=Counter()
        if len(factors(m))==1: expected[next(iter(factors(m)))]=1
        assert same(S,expected) and same(small,rep) and same(large,switch)
        cases+=1
for N in range(4,302,2):
    for q in range(2,101):
        if not any(e>=2 and N%p for p,e in factors(q).items()): continue
        p=next(p for p,e in factors(q).items() if e>=2 and N%p)
        a=next(a for a in range(q) if gcd(a,q)==1 and (a-N)%(p*p)==0)
        assert all(mu(N-n)==0 for n in range(a,N,q) if 1<=n<N)
        zero_classes+=1
print(f"PASS: {cases} symbolic identities, {terms} regrouped terms, {zero_classes} annihilating classes")
