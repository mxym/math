#!/usr/bin/env python3
"""Exact synthetic coefficient and order-averaging checks."""
from fractions import Fraction as F
from itertools import product
from random import Random


def theta_product(n):
    p=[F(1)]+[F(0)]*n
    for j in range(1,n+1):
        for k in (2*j,2*j-1,2*j-1):
            if k>n:
                continue
            for r in range(n,k-1,-1):
                p[r]-=p[r-k]
    s=[F(0)]*(n+1)
    s[0]=1
    for j in range(1,n+1):
        if j*j>n:
            break
        s[j*j]=2*(-1)**j
    assert p==s
    return n+1


def fisher(n):
    # Angular Fisher coefficients from b*d(db)-entropy and from
    # the double derivative of the log-density cosine series.
    ent=[F(0)]*(n+1)
    direct=[F(0)]*(n+1)
    for j in range(1,n+1):
        for k in range(1,n//(2*j)+1):
            ent[2*j*k]-=F(1,k)
        init=j*(j+1)
        if init>n:
            continue
        for m in range(init,n+1,2*j):
            ent[m]+=F(2*(-1)**(j+1),j)
            direct[m]+=2*(-1)**(j+1)*j
    assert [j*x for j,x in enumerate(ent)]==direct
    return n+1


def shifted(v):
    return (-v[-1],)+tuple(v[:-1])


def cyclic_module(q, d, gen):
    cols=[tuple(gen)]
    for _ in range(d-1):
        cols.append(shifted(cols[-1]))
    return {tuple(sum(c*x for c,x in zip(v,cols_i))%q
                  for cols_i in zip(*cols))
            for v in product(range(q),repeat=d)}


def fiber_sizes(q, J, order):
    last={()}
    sizes=[]
    for j in range(1,len(order)+1):
        nxt={tuple(v[t] for t in order[:j]) for v in J}
        assert len(nxt)%len(last)==0
        size=len(nxt)//len(last)
        assert q%size==0
        sizes.append(size)
        last=nxt
    return sizes


def cycle_checks():
    rng=Random(718)
    rows=0
    for q,d in ((2,4),(3,3),(3,4),(5,2),(5,4),(6,3),(9,2)):
        for _ in range(75):
            J=cyclic_module(q,d,[rng.randrange(q) for _ in range(d)])
            sizes=fiber_sizes(q,J,list(range(d)))
            pr=[1]*d
            for r in range(d):
                order=[(r+i)%d for i in range(d)]
                check=fiber_sizes(q,J,order)
                assert check==sizes
                for i,k in zip(order,check):
                    pr[i]*=k
                rows+=1
            assert all(k==len(J) for k in pr)
            projections=[len({v[i] for v in J}) for i in range(d)]
            assert len(set(projections))==1
            size=projections[0]
            if size**d==len(J):
                assert all(k==size for k in sizes)
    return rows


if __name__=="__main__":
    print("PASS exact theta4 / Fisher coefficients:",theta_product(220),fisher(260))
    print("PASS cyclic order and fiber rows:",cycle_checks())
