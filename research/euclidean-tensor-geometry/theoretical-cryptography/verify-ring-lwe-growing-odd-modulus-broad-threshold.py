#!/usr/bin/env python3
"""Exact synthetic checks for the growing-modulus information bound."""
from fractions import Fraction as F
from itertools import product, permutations
from math import comb


def xshift(a):
    return (-a[-1],)+tuple(a[:-1])


def columns(a):
    r=[tuple(a)]
    for _ in range(len(a)-1):
        r.append(xshift(r[-1]))
    return r


def norm(a):
    c=columns(a)
    total=0
    for p in permutations(range(len(a))):
        s=(-1)**sum(p[j]>p[k] for j in range(len(a))
                    for k in range(j+1,len(a)))
        v=s
        for j,k in enumerate(p):
            v*=c[j][k]
        total+=v
    return abs(total)


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def norm_checks():
    rows=size_tests=0
    for d,q in ((2,3),(2,5),(2,9),(4,3),(4,5)):
        for gen in ((1,)+(0,)*(d-1),
                    (1,1)+(0,)*(d-2),
                    (2,1)+(0,)*(d-2),
                    tuple(1 if i%2==0 else 0 for i in range(d)),
                    (q,)+(0,)*(d-1)):
            a=columns(gen)
            size=sum(all(dot(u,v)%q==0 for v in a)
                     for u in product(range(q),repeat=d))
            assert q**d%size==0
            index=q**d//size
            image={tuple(sum(u[j]*a[j][i] for j in range(d))%q
                         for i in range(d))
                   for u in product(range(q),repeat=d)}
            assert len(image)==index
            for u in product(range(-2,3),repeat=d):
                if not any(u) or any(dot(u,v)%q for v in a):
                    continue
                N=norm(u)
                assert N>0 and N%index==0
                assert N*N<=sum(t*t for t in u)**d
                rows+=1
            size_tests+=1
    return rows,size_tests


def order(a,m):
    for r in range(1,m+1):
        if pow(a,r,m)==1:
            return r
    raise AssertionError((a,m))


def v2(a):
    j=0
    while a%2==0:
        a//=2
        j+=1
    return j


def counts_checks():
    rows=0
    for d in (2,4,8,16,32,64,128,256,512):
        ps=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97)
        nf=[]
        for p in ps:
            f=order(p,2*d)
            assert d%f==0
            N=p**f
            assert N%(2*d)==1 and N>=2*d+1
            if d>=2**v2(p*p-1):
                assert f==4*d//(2**v2(p*p-1))
                assert f*(p*p-1)>=4*d
            nf.append(N)
            rows+=1
        assert len(set(nf))==len(nf)
        assert all(N>=1+2*d*j for j,N in enumerate(sorted(nf),1))
    prod_checks=0
    for d,pe in ((2,((3,2),(5,1))), (4,((3,1),(5,2))),
                 (8,((3,2),(17,1))), (16,((7,2),(17,1)))):
        acc=F(1)
        factors=[]
        for p,e in pe:
            f=order(p,2*d)
            for _ in range(d//f):
                fac=[p**(f*j) for j in range(e+1)]
                factors.append(fac)
                acc*=sum(F(1,u**3) for u in fac)
        def getprod(v):
            z=1
            for x in v:
                z*=x
            return z
        assert sum(F(1,getprod(v)**3) for v in product(*factors))==acc
        prod_checks+=1
    return rows,prod_checks


def moment_checks():
    rows=0
    for k in (1,2,3,6,17):
        p=2*k
        delta=F(1,2**(p+2))
        coeff=[F(0)]*(p+1)
        for j in range(2,p+1):
            c=comb(p,j)*delta**j
            if j%2:
                coeff[j-1]+=c/2
                coeff[j+1]+=c/2
            else:
                coeff[j]+=c
        for j in range(2,p+1,2):
            assert coeff[j]<=comb(k,j//2)
            rows+=1
    return rows


if __name__=="__main__":
    print("PASS norm/divisibility rows and dual indices:",norm_checks())
    print("PASS residue order and geometric product rows:",counts_checks())
    print("PASS even-moment domination coefficients:",moment_checks())
