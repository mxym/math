#!/usr/bin/env python3
"""Exact integer crossing at each parity, using independent binomial calls."""
from math import comb


def v(n,k):
    return sum(comb(n,i) for i in range(k+1))


def ratio(n,t):
    assert n>=t and (n-t)%2==0
    return v(n,(n-t)//2)*v(n,t-2), (1<<n)*v(n,t-3)


def above(n,t):
    a,b=ratio(n,t)
    return a>b


def crossing(t):
    assert not above(t,t)
    h=1
    while not above(t+2*h,t):
        h*=2
    lo,hi=0,h
    while hi-lo>1:
        m=(lo+hi)//2
        if above(t+2*m,t):
            hi=m
        else:
            lo=m
    n=t+2*hi
    assert not above(n-2,t) and above(n,t)
    return n


def main():
    symbolic={}
    monotone=0
    for t in range(3,61):
        n=crossing(t)
        assert n+1<=(t+1)**2
        symbolic[t]=n
        T=tuple(ratio(j,t) for j in range(t,t+24,2))
        for (a,b),(c,d) in zip(T,T[1:]):
            assert a*d<b*c
            monotone+=1
    print("EXACT: first N crossing for t=3,4,5,8,16,32,60:",
          ",".join(str(symbolic[t]) for t in (3,4,5,8,16,32,60)))
    assert 7**14*15**15>2**96
    W=[0b0000,0b1111,0b0001,0b1110]
    assert all((x^y).bit_count()!=2 for i,x in enumerate(W) for y in W[:i])
    print(f"EXACT: {len(symbolic)} threshold brackets, {monotone} strict monotonic comparisons, two lower-range checks PASS")


if __name__=="__main__":
    main()
