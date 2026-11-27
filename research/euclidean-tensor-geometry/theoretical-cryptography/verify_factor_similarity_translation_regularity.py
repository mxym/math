#!/usr/bin/env python3
"""Exact fixtures for bad-center projection and translation bounds."""
from fractions import Fraction as F
from itertools import product

checks=0


def check(p):
    global checks
    checks+=1
    if not p:
        raise AssertionError("exact check failed")


def merge(U):
    R=[]
    for a,b in sorted(U):
        if not R or R[-1][1]<a:
            R.append((a,b))
        else:
            R[-1]=(R[-1][0],max(b,R[-1][1]))
    return R


def length(U):
    return sum((b-a for a,b in merge(U)),F(0))


def cross(U,V):
    return [(max(a,c),min(b,d)) for a,b in U for c,d in V
            if max(a,c)<=min(b,d)]


def clip(P,a,b,c):
    """Clip a (possibly degenerate) convex polygon to ax+bt+c>=0."""
    if not P:
        return []
    R=[]
    for (x,t),(y,s) in zip(P[-1:]+P[:-1],P):
        f,g=a*x+b*t+c,a*y+b*s+c
        if (f<0)!=(g<0):
            u=f/(f-g)
            R.append((x+u*(y-x),t+u*(s-t)))
        if g>=0:
            R.append((y,s))
    return R


def project(C,q,I):
    # B+ complement lifted to the chart is the union of closed intervals C.
    P=[(F(0),F(1)),(F(1),F(1)),(F(1),F(2)),(F(0),F(2))]
    state=[P]
    for n in I:
        V=[]
        for Q,(a,b) in product(state,C):
            R=clip(clip(Q,F(1),q**n,-a),F(-1),-q**n,b)
            if R:
                V.append(R)
        state=V
    return merge((min(x for x,t in P),max(x for x,t in P)) for P in state)


def direct(x,C,q,I):
    """Independently intersect the feasible dilation intervals at a center."""
    S=[(F(1),F(2))]
    for n in I:
        S=cross(S,[((a-x)/q**n,(b-x)/q**n) for a,b in C])
    return bool(S)


def modulus_fixture(B,h):
    # Moving a union of disjoint circle arcs; intervals can cross the cut.
    C=[(F(0),F(1))]
    B=merge(B)
    T=merge(cross(C,[(a+h+j,b+h+j) for a,b in B for j in (-1,0,1)]))
    return length(B)+length(T)-2*length(cross(B,T))


def main():
    for N in (3,4,8,11):
        for mask in range(1,1<<min(N,4)):
            B0=[(F(i,N),F(i+1,N)) for i in range(N) if (mask>>(i%4))&1]
            B0=merge(B0)
            for l in range(-20,21):
                h=F(l,32)
                d=modulus_fixture(B0,h)
                check(0<=d<=min(2*length(B0),2*len(B0)*abs(h)))
                check(d==modulus_fixture(B0,-h))

    qvals=(F(1,2),F(2,3),F(3,5))
    # Degenerate pieces (singletons) in the closed complement are allowed.
    for base in ([(F(0),F(1,5)),(F(1,2),F(7,8))],
                 [(F(1,4),F(1,4)),(F(5,8),F(1))],
                 [(F(0),F(3,7)),(F(2,3),F(1))]):
        C=merge((a+j,b+j) for a,b in base for j in range(3))
        for q,I in product(qvals,[(1,),(2,3),(2,4,5),(1,2,4,6)]):
            R=project(C,q,I)
            K=4*(2*len(C)*len(I)+4)**2
            check(len(R)<=K)
            for x in {F(i,100) for i in range(101)}|{x for r in R for x in r}:
                check(direct(x,C,q,I)==any(a<=x<=b for a,b in R))
            p=F(1,91)
            if R:
                r=p/F(4*K)
                V=merge((a-r,b+r) for a,b in R)
                check(length(V)-length(R)<=p/2)
                n=1
                while 2*q**n>=r:
                    n+=1
                for a,b in R:
                    for x,t in product((a,(a+b)/2,b),(F(1),F(4,3),F(2))):
                        check(any(c<x+t*q**n<d for c,d in V))

    # Annular normalization: exact changes of variables and 1/h weights.
    intervals=[(F(1,500),F(1,70)),(F(2,57),F(1,8)),(F(2,9),F(11,40))]
    for q,b in product(qvals,(F(1),F(1,4),F(1,7))):
        prev=b
        for n in range(1,40):
            w=q**n
            Y=[(w*b,prev)]
            M=length(cross(Y,intervals))
            goodside=length(cross([(b,b/q)],[(a/w,c/w) for a,c in intervals]))
            check(goodside==M/w)
            for h in (w*b,(w*b+prev)/2,prev):
                check(b/h<=1/w<=b/(q*h))
            prev=w*b
    print(f"Translation regularity fixtures passed: {checks} exact assertions.")


if __name__=="__main__":
    main()
