#!/usr/bin/env python3
"""Exact small-degree checks for the HSOP line-by-tree Euler product."""
from fractions import Fraction
from math import isqrt
from sys import argv


def least_prime(n):
    assert n >= 2
    for p in range(2,isqrt(n)+1):
        if n%p == 0:
            return p
    return n


def generators(max_degree):
    # Each triple is (weight, parent, child) in formal q-integer exponents.
    rows = []
    relations = []
    for u in range(1,max_degree+1):
        rows.append((u,u,2*u))
    for r in range(3,2*max_degree+1,2):
        p = least_prime(r)
        t = r//p
        s=1
        while s*(r-t) <= max_degree:
            rows.append((s*(r-t),s*t,s*r))
            if s*(2*r-t) <= max_degree:
                relations.append(s*(2*r-t))
            s *= 2
    return rows,relations


def product_counts(degree, rows, relations):
    b=[1]+[0]*degree
    for w,_,_ in rows:
        for d in range(w,degree+1):
            b[d] += b[d-w]
    for w in relations:
        for d in range(degree,w-1,-1):
            b[d] -= b[d-w]
    return b


def brute_counts(N, rows):
    # Distinct products are distinguished by signed exponents of q-integers.
    # Each exponent lies between -N and N, so the radix encoding is injective.
    B=2*N+2
    powB=[B**i for i in range(2*N+1)]
    moves=[(w,powB[v]-powB[u]) for w,u,v in rows]
    D=[{0}]+[set() for _ in range(N)]
    for k in range(1,N+1):
        for w,z in moves:
            if w<=k:
                D[k].update(a+z for a in D[k-w])
    return [len(d) for d in D]


def exact_density(P):
    # D=1+sum(h_p/[p(p-1)])+sum_odd(h_p/[(p-1)(2p-1)]).
    # The two tails are each at most h_{>P}/P.
    H=Fraction(1)
    base=Fraction(1)
    gain=Fraction(0)
    for p in range(2,P+1):
        if least_prime(p)!=p:
            continue
        base+=H/Fraction(p*(p-1))
        if p>2:
            gain+=H/Fraction((p-1)*(2*p-1))
        H*=Fraction(p-1,p)
    return base, gain, 2*H/P


def main():
    N=int(argv[1]) if len(argv)>1 else 28
    assert N>=1
    A,R=generators(N)
    one=product_counts(N,A,R)
    two=brute_counts(N,A)
    assert one==two
    print("exact counts, degrees 0 through",N,":",one)
    m,g,e=exact_density(4000)
    assert Fraction(16783,10000) < m+g < m+g+e < Fraction(16785,10000)
    print("rigorous density interval [lower, upper]:",
          float(m+g), float(m+g+e), "(decimal display)")
    print("PASS")


if __name__=="__main__":
    main()
