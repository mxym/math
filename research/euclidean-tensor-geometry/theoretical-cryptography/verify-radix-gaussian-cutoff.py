#!/usr/bin/env python3
"""Reproduction checks for the radix Gaussian cutoff note."""
from fractions import Fraction as F
from itertools import product
from math import erf, exp, log, pi, sqrt
import numpy as np


def inv_scaled(k,b):
    q=F(1,b)
    return [[q**abs(i-j)*(1-q**(2*min(i,j)))*(1-q**(2*(k+1-max(i,j))))/(1-q**(2*(k+1)))
             for j in range(1,k+1)] for i in range(1,k+1)]


def dual(k,b):
    a=tuple(b**i for i in range(k+1))
    S=sum(x*x for x in a)
    ws=[]
    for i in range(1,k+1):
        h0=F(1,b**i)*(1-F(sum(a[j]**2 for j in range(i)),S))
        ws.append(tuple(a[j]*h0-(b**(j-i) if j>=i else 0) for j in range(k+1)))
    return a,S,ws


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


rng=np.random.default_rng(820735)
grams=glues=digits=0
for b in (3,4,5,7):
    for k in range(1,14):
        C=inv_scaled(k,b)
        a,S,W=dual(k,b)
        for i in range(k):
            assert dot(W[i],a)==0
            for j in range(k):
                expected=(b*b-1)*int(i==j)
                got=(b*b+1)*C[i][j]
                if i>0:
                    got-=b*C[i-1][j]
                if i<k-1:
                    got-=b*C[i+1][j]
                assert got==expected
                assert dot(W[i],W[j])==C[i][j]/(b*b-1)
                assert b*W[i][j]-W[i][j+1]==int(i==j)
                if k>=2 and i!=j:
                    c=F(27,50)
                    assert (C[i][i]-c)*(C[j][j]-c)>C[i][j]**2
                grams+=1
        for _ in range(50):
            zs=tuple(int(x) for x in rng.integers(-4,5,k))
            h=int(rng.integers(-3,4))
            w=tuple(sum(z*W[i][j] for i,z in enumerate(zs)) for j in range(k+1))
            x=tuple(wi+(h-w[0])*ai for wi,ai in zip(w,a))
            assert all(xx.denominator==1 for xx in x)
            assert x[0]==h
            assert dot(x,x)==dot(w,w)+S*(h-w[0])**2
            assert tuple(xx-F(dot(a,x),S)*aa for xx,aa in zip(x,a))==w
            glues+=1
        if 3<=k<=7:
            # Interior base-b signed digits have unique sums when subtracting
            # two +/-1 digits, as used before estimating the Gaussian phases.
            J=range(2,k)
            for vv in product(range(-2,3),repeat=len(J)):
                if not any(vv):
                    continue
                rr=sum(F(v,b**j) for v,j in zip(vv,J))
                assert abs(rr)>=F(1,b**(k-1))
                digits+=1

fibers=0
for b in (3,4):
    for k in range(1,4):
        a,S,W=dual(k,b)
        bs=np.array([float(w[0]) for w in W])
        C=np.array([[float(c)/(b*b-1) for c in row] for row in inv_scaled(k,b)])
        zs=np.array(list(product(range(-9,10),repeat=k)),dtype=float)
        freqs=zs@bs
        eng=np.einsum('ki,ij,kj->k',zs,C,zs)
        Y=np.array((-31,-18,-5,-1,0,1,5,18,31))
        for t in (2.,2.7,3.8):
            M=20
            supp=np.arange(-M,M+1)
            z0=np.exp(-pi*(supp/t)**2)
            p=np.array([1.])
            for ai in a:
                stretch=np.zeros(2*M*ai+1)
                stretch[::ai]=z0/sum(z0)
                p=np.convolve(p,stretch)
            center=M*sum(a)
            # In these toy widths all omitted ambient and line terms
            # are below the displayed tolerance.
            mm=(sum(np.exp(-pi*t*t*supp*supp)))**(k+1)
            mm/=sum(np.exp(-pi*t*t*S*supp*supp))
            Q=np.exp(-pi*Y*Y/(t*t*S))/(t*sqrt(S)*sum(np.exp(-pi*t*t*S*supp*supp)))
            F_y=np.exp(-pi*t*t*eng)@np.cos(2*pi*freqs[:,None]*Y[None,:])
            assert np.max(np.abs(p[center+Y]/Q-F_y/mm))<1e-8
            fibers+=len(Y)

mc=0
for b in (3,4,7):
    for tau in (.4,1.5,3.):
        k=2500
        eps=sqrt(tau/k)
        u=np.zeros(9500)
        logs=np.zeros_like(u)
        for _ in range(k):
            u=(u+rng.integers(b,size=len(u)))/b
            logs+=np.log1p(2*eps*np.cos(2*pi*u))
        tv=np.mean(np.maximum(0,1-np.exp(logs)))
        expected=erf(sqrt(tau)/2)
        assert abs(tv-expected)<.03
        assert abs(np.mean(logs)+tau)<.09
        mc+=1

print("PASS exact Gram entries",grams,"integer decompositions",glues)
print("PASS exact signed digit differences",digits,"finite likelihood comparisons",fibers)
print("PASS seeded limiting digit statistics",mc)
