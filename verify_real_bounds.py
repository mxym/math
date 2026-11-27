#!/usr/bin/env python3
"""Proof checker for the small scalar real-power inequalities.

All sign decisions use integer interval arithmetic; no float or sampled-sign
heuristic is used. Each accepted interval encloses the full continuous range.
"""
from fractions import Fraction as F
from functools import lru_cache

S = 1 << 100


def ceil(n, d):
    return -((-n) // d)


def enclosure(lo, hi):
    return lo.numerator*S//lo.denominator, ceil(hi.numerator*S, hi.denominator)


@lru_cache(None)
def log(a):
    t = F(a-1, a+1)
    t2 = t*t
    u = t
    v = F(0)
    for i in range(128):
        v += 2*u/(2*i+1)
        u *= t2
    return enclosure(v, v+2*u/(257*(1-t2)))


def exp(lo, hi):
    assert 0 <= lo <= hi <= 8*S
    l = u = tl = tu = S
    for j in range(1,65):
        tl = tl*lo//(j*S)
        tu = ceil(tu*hi,j*S)
        l += tl
        u += tu
    u += 2 * ceil(tu*hi,65*S)
    return l,u


@lru_cache(None)
def power(a, q):
    v,w=log(a)
    return exp(v*q.numerator//q.denominator,ceil(w*q.numerator,q.denominator))


def mulpos(v,w):
    return v[0]*w[0]//S,ceil(v[1]*w[1],S)


def ev(P, lo, hi, d=0):
    ll=uu=0
    assert 0 < lo <= hi <= 2
    for a,c in P.items():
        v = power(a,lo)[0], power(a,hi)[1]
        for i in range(d):
            v = mulpos(v,log(a))
        if c<0:
            ll+=c*v[1]
            uu+=c*v[0]
        else:
            ll+=c*v[0]
            uu+=c*v[1]
    return ll,uu


def sub(a,b):
    return {i:a.get(i,0)-b.get(i,0) for i in a.keys()|b.keys()}


def certify(P, a, b, sign=1, d=0):
    stack = [(a,b,0)]
    n = 0
    while stack:
        l,h,depth = stack.pop()
        lo,hi = ev(P,l,h,d)
        if lo>0 if sign>0 else hi<0:
            n += 1
            continue
        assert depth<20, (P,a,b,l,h,d,lo,hi)
        m=(l+h)/2
        stack.extend(((l,m,depth+1),(m,h,depth+1)))
    return n


def roots(P, lo, hi):
    assert ev(P,lo,lo)[1]<0<ev(P,hi,hi)[0]
    for _ in range(35):
        m=(lo+hi)/2
        a,b=ev(P,m,m)
        if a>0:
            hi=m
        else:
            assert b<0, (P,m,a,b)
            lo=m
    return lo,hi


def decimals(lo, hi, places=9):
    k=10**places
    a=lo.numerator*k//lo.denominator
    b=ceil(hi.numerator*k,hi.denominator)
    return f"[{a//k}.{a%k:0{places}d},{b//k}.{b%k:0{places}d}]"


def main():
    for a in range(1,10):
        for n in (1,2):
            lo,hi=power(a,F(n))
            assert lo<=a**n*S<=hi
    assert 3**3>4**2                         # slope of 3^r-1-4^r/2 at r=1
    assert 2**56<3**36                        # slope of mixed comparison at r=2
    assert 5**15>3**9*7**7                    # slope of slope-gap at r=1
    assert 3**54*7**49<5**100                 # slope of 2*beta-delta_7 at r=2

    A,B,C,D = {4:63},{3:35,5:28},{2:19,4:32,6:12},{4:48,8:4}
    O = {1:11,3:24,5:24,7:4}
    g = {1:-3,3:7,5:-7,7:4,9:-1}
    assert sum(g[i]*i for i in g)==2
    assert sum(g[i]*i*i for i in g)==0
    print("delta_9 >= 4*delta_7: concavity certificate:",certify(g,F(1),F(2),-1,2))

    for name,P in [("C-B",sub(C,B)),("D-C",sub(D,C))]:
        k=certify(P,F(1),F(9,5),-1)
        j=certify(P,F(9,5),F(2),1,1)
        print(name,": negative then strictly increasing; interval leaves",k,j)

    cuts = [F(1),F(189,100),F(191,100),F(3853,2000),F(2)]
    for name,P,l,h in zip("ABCD",(A,B,C,D),cuts,cuts[1:]):
        print(name+"-O",": positive; interval leaves",certify(sub(P,O),l,h))
    assert ev(sub(D,O),F(1),F(1))[1]<0  # invalid global comparison is rejected

    intervals=[(1887,1888),(1908,1909),(1926,1927)]
    for name,P,(s,t) in zip(("B-A","C-B","D-C"),(sub(B,A),sub(C,B),sub(D,C)),intervals):
        lo,hi=roots(P,F(s,1000),F(t,1000))
        print(name,"crosses at r in",decimals(lo,hi),"and p in",decimals(hi/(hi-1),lo/(lo-1)))
    print("PASS: every real-interval, root, and negative-control claim")


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Do not run with Python -O.")
    main()
