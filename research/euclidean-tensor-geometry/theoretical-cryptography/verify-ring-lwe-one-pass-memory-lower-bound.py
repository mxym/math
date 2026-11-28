#!/usr/bin/env python3
"""Synthetic exact Fourier and exponent checks for the streaming bound."""
from collections import Counter
from fractions import Fraction as F
from itertools import product


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def mult(a,b,q):
    d=len(a)
    c=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            k=i+j
            if k>=d:
                c[k-d]-=x*y
            else:
                c[k]+=x*y
    return tuple(x%q for x in c)


def adj(a,q):
    return (a[0],)+tuple((-x)%q for x in a[:0:-1])


def char_square(pts,k,weight,q):
    a=Counter()
    for x in pts:
        a[dot(x,k)%q]+=weight[x]
    return tuple(sum(a[i]*a[(i-r)%q] for i in range(q)) for r in range(q))


def exact_extraction_checks():
    pairs=means=0
    for q,d in ((3,2),(5,2),(9,2),(3,4)):
        pts=list(product(range(q),repeat=d))
        w={x:1+(sum((i+1)*v*v for i,v in enumerate(x))%13) for x in pts}
        spec={k:char_square(pts,k,w,q) for k in pts}
        units=[tuple(int(i==j) for i in range(d)) for j in range(d)]
        tab={a:[mult(a,e,q) for e in units] for a in pts}
        for u in pts:
            images=Counter()
            for a in pts:
                z=mult(adj(a,q),u,q)
                explicit=tuple(dot(c,u)%q for c in tab[a])
                assert z==explicit
                images[z]+=1
                pairs+=1
            ideal={mult(a,u,q) for a in pts}
            assert set(images)==ideal
            assert set(images.values())=={len(pts)//len(ideal)}
            # Sum in the integral group ring of the additive frequency
            # index, before evaluating at a complex root of unity.
            for k in range(q):
                av1=F(sum(m*spec[y][k] for y,m in images.items()),len(pts))
                av2=F(sum(spec[y][k] for y in ideal),len(ideal))
                assert av1==av2
                means+=1
    return pairs,means


def moment_bound_checks():
    rows=0
    # Scale all exponents by x=r d, which need not be an integer.
    for x,a,b in product((F(121,3),F(1134,5),F(1003),F(100071,18)),
                         range(1,50),range(1,30)):
        ell_d=x/64
        L=ell_d*F(a,16*a+b)
        l=F(x,8*L)
        k=l.numerator//l.denominator
        assert F(x,16*L)<=k and k*L<=x/8
        logW=ell_d*x/(32*L)
        logT=x/64
        quantity=logW+2*logT+x/8-2*ell_d*k
        assert quantity < -x
        assert 3*ell_d+x/8+L<x
        rows+=1
    return rows


if __name__=="__main__":
    print("PASS finite adjoints / exact ideal Fourier means:",exact_extraction_checks())
    print("PASS rational overlap-moment exponent rows:",moment_bound_checks())
