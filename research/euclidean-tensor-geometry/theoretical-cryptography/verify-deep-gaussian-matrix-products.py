#!/usr/bin/env python3
"""Exact finite checks for the arbitrary-depth Gaussian matrix product note."""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from collections import Counter
from math import prod

def eye(n):
    return [[F(int(i==j)) for j in range(n)] for i in range(n)]

def mm(A,B):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]

def ad(A,B,c=1):
    return [[x+c*y for x,y in zip(a,b)] for a,b in zip(A,B)]

def tr(A):
    return sum(r[i] for i,r in enumerate(A))

def norm2(A):
    return sum(x*x for row in A for x in row)

def elim(A):
    B=[list(r) for r in A]
    I=eye(len(A))
    d=F(1)
    for i in range(len(B)):
        t=B[i][i]
        assert t
        d*=t
        B[i]=[x/t for x in B[i]]
        I[i]=[x/t for x in I[i]]
        for j in range(len(B)):
            if i==j:
                continue
            t=B[j][i]
            B[j]=[x-t*y for x,y in zip(B[j],B[i])]
            I[j]=[x-t*y for x,y in zip(I[j],I[i])]
    return I,d

def cov(i,j,k,l):
    return int(i==k and j==l)+int(i==l and j==k)

def sym(n,z):
    return [[F(((i+1)*(j+1)+z+7*abs(i-j))%11-5,37)
             for j in range(n)] for i in range(n)]

N1=N2=N3=0
for n in range(1,6):
    I=eye(n)
    for v in range(20):
        B=sym(n,v)
        R=ad(I,sym(n,2*v+1))
        C=ad(mm(mm(R,B),R),B,-1)
        for d in (1,3,17,69):
            # Variance of the exact centered scalar Wishart increment.
            s=sum(C[i][j]*C[k][l]*cov(i,j,k,l)/d
                  for i,j,k,l in product(range(n),repeat=4))
            assert s==2*norm2(C)/d
            N1+=1
            # Conditional second trace in the likelihood overlap.
            x=sum(B[i][j]*B[k][l]*cov(j,k,l,i)/d
                  for i,j,k,l in product(range(n),repeat=4))
            assert x==(tr(mm(B,B))+tr(B)**2)/d
            N2+=1
        X=B
        Y=sym(n,3*v+4)
        Ai,da=elim(ad(I,X)); Bi,db=elim(ad(I,Y))
        _,dc=elim(ad(ad(Ai,Bi),I,-1))
        _,de=elim(ad(I,mm(X,Y),-1))
        assert da*db*dc==de
        N3+=1

def raw_z(d,r):
    return prod(1+F(2*j,d) for j in range(r))

# For integer t, the exact gamma ratio is a polynomial in 1/d.
# Evaluate its first-order coefficient by exact polynomial enumeration.
N4=0
for t in range(1,12):
    for k in (1,2,4,7,16,31):
        widths=[3+(2*j*j+7*j+t)%99 for j in range(k)]
        coeff=[F(1),F(0)]
        for d in widths:
            for j in range(t):
                a=F(2*j,d)
                coeff[1]+=a*coeff[0]
        assert coeff[1]==(t*t-t)*sum(F(1,d) for d in widths)
        assert all(raw_z(d,t)>=1 for d in widths)
        N4+=1

# Exhaust the small rectangle diagrams in the fourth moment calculation:
# repeated-pair correction and four-distinct supports are separate.
N5=N6=0
for p,q in ((2,2),(2,4),(3,3),(3,4),(4,4),(4,5)):
    cells=[frozenset(product(rows,cols))
           for rows in combinations(range(p),2)
           for cols in combinations(range(q),2)]
    n=len(cells)
    n2=sum(6*3**len(A & B) for A,B in combinations(cells,2))
    assert n2>=3*n*(n-1)
    for inds in combinations(cells,4):
        A,B,C,D=inds
        N5+=1
        if A ^ B ^ C ^ D:
            continue
        rows={i for i,j in set.union(*(set(Z) for Z in inds))}
        cols={j for i,j in set.union(*(set(Z) for Z in inds))}
        assert len(rows)<=4 and len(cols)<=4
        assert len(rows)<4 or len(cols)<4
        N6+=1

print("PASS: Wishart variance, quadratic contraction, precision determinant =",N1,N2,N3)
print("PASS: arbitrary-length scalar gamma coefficient tables =",N4)
print("PASS: four-distinct rectangle diagrams, nonzero contributions =",N5,N6)
