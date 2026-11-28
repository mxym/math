#!/usr/bin/env python3
"""Finite arithmetic checks for the abstract dyadic hard-edge theorem."""
from fractions import Fraction as F
from itertools import permutations,product
from math import comb,factorial,gcd,prod
from random import Random


def compress(n,a):
    k=len(a)
    M=1
    while (M+1)**(2*k)<=n:
        M+=1
    boxes={}
    for t in range(M**k+1):
        box=tuple(((t*q)%(2*n))*M//(2*n) for q in a)
        if box in boxes:
            h=t-boxes[box]
            break
        boxes[box]=t
    else:
        raise AssertionError("Dirichlet pigeonhole")
    g=gcd(h,2*n)
    L=2*n//g
    b=[((q*(h//g)+L//2)%L)-L//2 for q in a]
    assert h<=M**k and L*L>=4*n
    assert all(i%2 and abs(i)*M<=L for i in b)
    assert all((h*q-g*i)%(2*n)==0 for q,i in zip(a,b))
    return M,h,g,L,b


def phase_checks():
    rng=Random(1729)
    rows=0
    unaliased=0
    for n,k in product((128,512,2048,8192),range(1,6)):
        for _ in range(37):
            a=rng.sample(range(1,n,2),k)
            M,h,g,L,b=compress(n,a)
            assert len({x for q in a for x in (q,2*n-q)})==2*k
            assert all((q*n)%(2*n)==n for q in a)
            for s in (0,1,3,7,L//2,L-1):
                start=rng.randrange(g)
                j=(start+h*s)%(2*n)
                for q,i in zip(a,b):
                    assert (q*j-q*start-g*i*s)%(2*n)==0
                    rows+=1
            if M>=3:
                # No squared-frequency alias at the discrete grid.
                for u,v in product(b+[-x for x in b],repeat=2):
                    assert ((u+v)%L==0) == (u+v==0)
                    unaliased+=1
    return rows,unaliased


def pmul(A,B,t):
    C=[0]*(t+1)
    for i,a in enumerate(A):
        for j,b in enumerate(B):
            if i+j<=t:
                C[i+j]+=a*b
    return C


def det_poly(A,t):
    n=len(A)
    C=[0]*(t+1)
    for p in permutations(range(n)):
        coeff=[1]
        sign=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        for i,j in enumerate(p):
            coeff=pmul(coeff,A[i][j],t)
        for i,c in enumerate(coeff):
            C[i]+=sign*c
    return C


def laguerre_checks():
    tests=0
    for r,alpha in product(range(1,6),range(6)):
        m=alpha+r
        d=alpha+1
        A=[[[comb(alpha,j)*factorial(i+k+alpha-j) for j in range(alpha+1)]
             for k in range(r)] for i in range(r)]
        C=det_poly(A,d)
        Z_over_fact=prod(factorial(i)*factorial(alpha+i) for i in range(r))
        assert C[0]==Z_over_fact
        # Exact survival P(lambda_min>x) = exp(-r*x)
        # times this determinant ratio, after shifting all eigenvalues.
        E=[F((-r)**j,factorial(j)) for j in range(d+1)]
        survival=pmul([F(c,C[0]) for c in C],E,d)
        target=F(factorial(m),factorial(r-1)*factorial(d)**2)
        assert survival==[1]+[0]*(d-1)+[-target]
        Z1=prod(factorial(i+1)*factorial(alpha+i) for i in range(r))
        Z2=prod(factorial(i+1)*factorial(alpha+2+i) for i in range(r-1))
        assert F(r*Z2,d*Z1)==target
        if alpha==0:
            assert target==r
        if r==1:
            assert target==F(1,factorial(m))
        tests+=1
    return tests


def main():
    print("PASS exact orbit phases and squared nonaliases:",phase_checks())
    print("PASS independent shifted-Wishart determinant hard-edge constants:",laguerre_checks())


if __name__=="__main__":
    main()
