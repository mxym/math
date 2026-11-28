#!/usr/bin/env python3
"""Exact algebra checks for exact-triangular-gaussian-four-thirds.md."""

from fractions import Fraction as Q
from itertools import product


def add(a,b,k=1):
    return tuple(x+k*y for x,y in zip(a,b))


def scale(k,a):
    return tuple(k*x for x in a)


def dot(a,b):
    return a[0]*b[0]+a[1]*b[1]+Q(a[0]*b[1]+a[1]*b[0],2)


def norm2(a):
    return dot(a,a)


def main():
    V = tuple(x for x in product(range(-6,7),repeat=2) if any(x))
    U = tuple(x for x in V if norm2(x)==1)
    low2 = tuple(x for x in V if norm2(x)==3)
    I = U + low2
    H = tuple(x for x in V if x not in I)
    assert len(U)==len(low2)==6
    assert all(norm2(x)>=4 for x in H)
    n1=n2=nH=0
    for j in V:
        p = max(dot(j,v) for v in U)
        assert p.denominator in (1,2)
        if j in H:
            assert p>=2
            assert (p==2)==any(j==scale(2,v) for v in U)
    for delta in map(Q,("1/4","1/8","1/16","1/31","1/97")):
        A=4-delta
        d=2-delta/4
        e=Q(1,2)-delta/4
        dp=A-d
        assert dp==2-3*delta/4
        assert 1-max((d-1)**2,e**2)>=delta/4
        for j in U:
            alpha=scale(d,j)
            zeta=add(alpha,j,-A)
            damp=(A-1)*(2*dot(alpha,j)-A)
            assert damp==(A-1)*delta/2
            for i in I:
                if i!=j:
                    assert norm2(add(i,alpha,-1))-(d-1)**2>=delta/4
                assert norm2(add(i,zeta,-1))+damp-(d-1)**2>=delta/2
                n1+=1
        for j in low2:
            choices=[v for v in U if dot(j,v)==Q(3,2)]
            assert len(choices)==2
            for v in choices:
                w=add(j,v,-1)
                assert w in U and dot(v,w)==Q(1,2)
                alpha=add(j,v,e)
                zeta=add(alpha,v,-A)
                damp=(A-1)*(2*dot(alpha,v)-A)
                assert damp==(A-1)*delta/2
                assert min(norm2(add(i,zeta,-1)) for i in V)==(Q(1,2)-3*delta/4)**2
                for i in V:
                    if i!=j:
                        assert norm2(add(i,alpha,-1))-e**2>=delta/2
                    assert norm2(add(i,zeta,-1))+damp-e**2>=delta
                    n2+=1
        for j in H:
            p=max(dot(j,v) for v in U)
            for v in U:
                if dot(j,v)!=p:
                    continue
                zeta=add(j,v,-A)
                damp=(A-1)*(2*p-A)
                for i in I:
                    assert norm2(add(j,i,-1))>=1
                    assert norm2(add(zeta,i,-1))+damp>=1
                    nH+=1
    print(f"PASS: {n1} unit-shell checks, {n2} second-shell checks, {nH} high-to-low checks")


if __name__=="__main__":
    main()
