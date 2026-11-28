#!/usr/bin/env python3
"""Replays exact constants and finite examples, not a lattice sampler."""
from collections import Counter
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import floor, gcd, isqrt, lcm
from random import Random

seen=Counter()


def exneg(x):
    assert 0 < x < 18
    t=s=F(1)
    for j in range(1,81):
        t *= x/j
        s += t
    T=t*x/81/(1-x/82)
    return 1/(s+T),1/s


m0=exneg(F(3,2))[0]
m1=exneg(F(9,2))[1]
m2=exneg(F(15))[1]
assert m0>F(223,1000) and m1<F(112,10000) and m2<F(1,10**6)
assert F(317,217)*exneg(F(33,2))[1] < F(1,50)
assert 217*m2/(1-F(1,50))<F(1,1000)
assert 83*m0-17-117*m1-F(1,1000)>0
p0=exneg(F(3,4))[1]
p1=exneg(F(15,2))[1]
assert p0<F(473,1000) and p1<F(1,1600)
assert F(8,5)*exneg(F(51,4))[1] < F(1,50)
assert -1+2*p0+5*p1/(1-F(1,50))<0
seen["exact strict checks"]+=9


def circ(x):
    t=x-floor(x)
    return min(t,1-t)


def grid(r):
    dd=lcm(*(x.denominator for x in r))
    assert gcd(dd,*(int(x*dd) for x in r if x))==1
    return dd


def nearest(al,r,d):
    u=r-floor(r)
    z=d*(F(1,2)-al-u/2)
    a=floor(z)
    return al+F(a+int(z-a>F(1,2)),d)


def dec(x):
    return D(x.numerator)/x.denominator


@lru_cache(None)
def probs(a,c):
    with localcontext() as ctx:
        ctx.prec=52
        n=round(c)
        xx=list(range(n-14,n+15))
        e=[(-dec(a*((v-c)**2-(n-c)**2))).exp() for v in xx]
        z=sum(e)
        return tuple((x,f/z) for x,f in zip(xx,e))


def mean(a,c):
    n=floor(c)
    return n+sum(x*w for x,w in probs(a,c-n))


def compare_all(a,al,rv):
    d=grid(rv)
    for r in rv:
        r=abs(r)
        c=nearest(al,r,d)
        y=mean(a,c+r)-mean(a,c)
        assert y>=0
        for j in range(d):
            cc=al+F(j,d)
            vv=mean(a,cc+r)-mean(a,cc)
            assert vv<=y+D("1e-42")
            seen["small grid comparisons"]+=1
        # Rebuild Wasserstein using the CDF expression, independent of mean.
        g=dict(probs(a,c+r))
        h=dict(probs(a,c))
        b=D(0)
        w=D(0)
        for z in range(min(g.keys()|h.keys()),max(g.keys()|h.keys())+1):
            b+=g.get(z,D(0))-h.get(z,D(0))
            w+=abs(b)
        assert abs(w-y)<D("1e-42")
        seen["CDF comparisons"]+=1


with localcontext() as ctx:
    ctx.prec=50
    rng=Random(478125)
    for i in range(42):
        a=rng.choice([F(3,4),F(1),F(2),F(3),F(5),F(9)])
        den=rng.randrange(3,31)
        rv=[F(rng.randrange(-2*den,2*den+1),den) for _ in range(3)]
        compare_all(a,F(rng.randrange(-37,38),rng.randrange(1,20)),rv)
    compare_all(F(3),F(0),[F(1,4),-F(1,4),F(1,4)])
    for d in range(2,10):
        for k in range(1,d):
            u=F(k,d)
            for al in (F(1,2), F(1,2)+F(1,4*d)):
                c=nearest(al,u,d)
                Dg=mean(F(1000),c+u)-mean(F(1000),c)
                lim=F(1,2) if k==1 and al==F(1,2) else F(1)
                assert abs(Dg-dec(lim))<D("1e-18")
                seen["cold limits"]+=1
    s=F(1,127)
    for j in range(160):
        # LCM can exceed the number of stored integers by many orders of magnitude.
        b=1_000_000_007*(1<<rng.randrange(10,200))+1
        rv=[F(2,b),F(-1,3*b),F(12331,7*b+1)]
        d=grid(rv)
        r=abs(rng.choice(rv))
        c=nearest(s,r,d)
        u=r-floor(r)
        t=c+u/2-F(1,2)
        assert abs(t)<= F(1,2*d)
        seen["large lcm choices"]+=1
        s+=F(1,37)

for a in (F(1,1<<200),F(7,1<<90),F(1,16),F(4,5),F(1),F(9),F(1<<80)):
    L=max(1,isqrt(a.denominator//a.numerator))
    if a*L*L<1:
        L+=1
    assert a*L*L>=1 and (L==1 or a*(L-1)**2<1)
    if a<=1:
        assert a*L*L<=4
    for z in (F(-1,2),F(-1,7),F(0),F(1,2)):
        for k in range(8):
            for g in {k*L,(k+1)*L-1}:
                assert a*(g*g+2*g*z)>=k*(k-1)
                seen["proposal exponent checks"]+=1
        if a<=1:
            for g in {-(L//2),0,L//2}:
                assert a*(g*g+2*g*z)<=4
                seen["near mode checks"]+=1
print("PASS reachable-center Gaussian influence checks:",dict(seen))
