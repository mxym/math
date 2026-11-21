"""Finite exact controls, with log of each prime an independent formal variable."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,gcd
from collections import Counter
def req(ok,msg):
    if not ok:raise ValueError(msg)
@lru_cache(None)
def fact(n):
    d=2;f=[]
    while d*d<=n:
        while n%d==0:f.append(d);n//=d
        d+=1
    if n>1:f.append(n)
    return tuple(f)
@lru_cache(None)
def divisors(n):return tuple(i for i in range(1,n+1) if n%i==0)
def mu(n):
    f=fact(n)
    return 0 if len(set(f))<len(f) else (-1)**len(f)
def phi(n):
    a=n
    for r in set(fact(n)):a=a//r*(r-1)
    return a
def pp(n):
    f=fact(n)
    return f[0] if f and f.count(f[0])==len(f) else 0
def rough(n,z):return not fact(n) or min(fact(n))>z
def vaughan(y,D,U,z):
    out=Counter()
    for d in divisors(y):
        v=y//d
        if d<=D and rough(d,z) and rough(v,z):
            for p in fact(v):out[p]+=mu(d)
        for k in divisors(v):
            ell=pp(k)
            if not ell or not all(rough(j,z) for j in (d,k,v//k)):continue
            if d<=D and k<=U:out[ell]-=mu(d)
            if d>D and k>U:out[ell]+=mu(d)
    if y<=U and pp(y) and rough(y,z):out[pp(y)]+=1
    return {p:k for p,k in out.items() if k}
for z in [1,2,3,5]:
    for y in range(1,520):
        a=({pp(y):1} if pp(y) and rough(y,z) else {})
        for D,U in [(10,5),(5,3),(4,11)]:
            req(vaughan(y,D,U,z)==a,'unequal cuts/rough source')
for d in range(1,90):
    if not mu(d):continue
    for k in range(2,95):
        r=pp(k)
        if r:req(Q(1,phi(d*k))==Q(1,phi(d)*phi(k))*(1-(Q(1,r) if d%r==0 else 0)),'local factor')
gap=Q(4,100*factorial(99))
req(10**13*gap+Q(1400,factorial(300))<Q(1,10**130),'fixed positive-sieve error budget')
print('Two source variants, exact local factors and the <10^-130 bound passed.')
