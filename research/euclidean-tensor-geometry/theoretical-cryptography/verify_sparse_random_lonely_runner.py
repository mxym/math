#!/usr/bin/env python3
"""Exact finite controls for the sparse random Lonely Runner proof."""
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod


def need(test, label):
    if not test:
        raise AssertionError(label)


def forbidden(N,p,a,delta):
    out=set()
    for v in range(1,N+1):
        r=a*v%p
        if min(r,p-r)<p*delta: out.add(v)
    return out


def rect(N,p,A,delta):
    # Independent count in the integer box with signed x_i coordinates.
    X=tuple(x for x in range(-p//2,p//2+1) if abs(x)<p*delta)
    return sum(all((x-a*v)%p==0 for a,x in zip(A,V))
               for v in range(1,N+1) for V in product(X,repeat=len(A)))


def grid_controls():
    cases=0
    for N,p,delta in ((5,11,Fraction(3,11)),(8,13,Fraction(1,5)),
                      (10,17,Fraction(5,17)),(12,19,Fraction(1,7))):
        sets=[forbidden(N,p,a,delta) for a in range(p)]
        for a in range(p):
            need(rect(N,p,(a,),delta)==len(sets[a]), ("single box",N,p,a))
            for b in range(p):
                need(rect(N,p,(a,b),delta)==len(sets[a]&sets[b]),
                     ("pair box",N,p,a,b))
                cases+=1
    print("exact grid overlap cases",cases)


def dual_controls():
    for p in (7,11,17):
        for d in (2,3):
            H=min(2,p-1)
            all_A=list(product(range(p),repeat=d-1))
            bads=set()
            seen=0
            for w in product(range(-H,H+1),repeat=d):
                if not any(w): continue
                matching={A for A in all_A
                          if (w[0]+sum(a*b for a,b in zip(A,w[1:])))%p==0}
                want=p**(d-2) if any(w[1:]) else 0
                need(len(matching)==want, ("dual affine equation fiber",p,w))
                bads|=matching;seen+=len(matching)
            need(len(bads)<=seen<=(2*H+1)**d*p**(d-2),
                 ("exceptional numerator union",p,d))
    print("dual-short-normal enumeration passed")


def cover_controls():
    for N in range(17,43):
        for p in (17,23,31):
            for a in range(p):
                for d in (Fraction(3,10),Fraction(2,5),Fraction(5,13)):
                    k=-(-2*d.denominator//d.numerator)
                    need(N+1>=2*k,"pigeonhole range")
                    B=forbidden(N,p,a,d)
                    values=[a*j%p for j in range(N+1)]
                    blocks=[v*k//p for v in values]
                    pair_count=sum(blocks[j]==blocks[i]
                                   for i,j in combinations(range(N+1),2))
                    need(pair_count>=Fraction((N+1)**2,4*k),"pair lower count")
                    need(all(j-i in B for i,j in combinations(range(N+1),2)
                             if blocks[j]==blocks[i]),"index difference map")
                    need(len(B)>=N*d/12,"uniform forbidden fraction")
    print("finite pigeonhole bounds passed")


def sample_controls():
    for N in range(3,85):
        for m in range(1,7):
            if m>N:continue
            for b in range(N+1):
                f=Fraction(comb(N-b,m),comb(N,m))
                w=Fraction(N-b,N)
                need(f<=w**m,"falling-factorial upper bound")
                if N-b>=m:
                    factors=prod(Fraction(1-Fraction(j,N-b),1-Fraction(j,N))
                                 for j in range(m))
                    need(f==w**m*factors,"falling-factorial factorization")
    print("exact fixed-size sampling controls passed")


if __name__=="__main__":
    grid_controls()
    dual_controls()
    cover_controls()
    sample_controls()
