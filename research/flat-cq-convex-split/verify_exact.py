#!/usr/bin/env python3
"""Exact Fraction tests for the moment and regularized Gram identities."""
from fractions import Fraction as F
from itertools import product, combinations
from functools import reduce


def Z(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def I(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def add(A, B):
    return [[a+b for a,b in zip(x,y)] for x,y in zip(A,B)]


def scale(t, A):
    return [[t*a for a in x] for x in A]


def mul(A, B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)]
            for row in A]


def outer(u, v):
    return [[a*b for b in v] for a in u]


def dot(u, v):
    return sum(a*b for a,b in zip(u,v))


def quad(v, A):
    return sum(v[i]*v[j]*A[i][j] for i,j in product(range(len(v)),repeat=2))


def inv(A):
    n=len(A)
    C=[x+y for x,y in zip(A,I(n))]
    for i in range(n):
        k=next(k for k in range(i,n) if C[k][i])
        C[i],C[k]=C[k],C[i]
        C[i]=[a/C[i][i] for a in C[i]]
        for k in range(n):
            if k!=i:
                u=C[k][i]
                C[k]=[a-u*b for a,b in zip(C[k],C[i])]
    return [x[n:] for x in C]


def det(A):
    if not A:
        return F(1)
    return sum((-1)**j*A[0][j]*det([r[:j]+r[j+1:] for r in A[1:]])
               for j in range(len(A)))


def is_psd(A):
    n=len(A)
    return A==list(map(list,zip(*A))) and all(
        det([[A[i][j] for j in s] for i in s])>=0
        for k in range(1,n+1) for s in combinations(range(n),k))


def total(matrices, n):
    return reduce(add,matrices,Z(n))


vec=[
    (F(1),F(0),F(0)),
    (F(0),F(1),F(0)),
    (F(0),F(0),F(1)),
    (F(3,5),F(4,5),F(0)),
    (F(3,5),-F(4,5),F(0)),
    (F(0),F(3,5),F(4,5)),
    (F(1,3),F(2,3),F(2,3)),
]
assert all(dot(v,v)==1 for v in vec)

gram_checks=0
for k in range(4):
    for idx in product(range(len(vec)),repeat=k):
        cols=[vec[i] for i in idx]
        S=total([outer(v,v) for v in cols],3)
        B=add(S,scale(-1,I(3)))
        Q=add(S,mul(B,B))
        T=mul(S,inv(Q))
        assert is_psd(T)
        assert is_psd(add(I(3),scale(-1,T)))
        assert is_psd(add(scale(F(4,3),S),scale(-1,T)))
        gram_checks+=3
        for i,u in enumerate(cols):
            g=sum(dot(u,v)**2 for j,v in enumerate(cols) if i!=j)
            for psi in vec:
                assert quad(psi,T)*(1+g)>=dot(u,psi)**2
                gram_checks+=1
print(f"exact regularized Gram and singular-support checks: {gram_checks}")

# A deliberately dependent pairwise-independent table: U,V,U XOR V.
table=[(u,v,u^v) for u,v in product(range(2),repeat=2)]
assert all(len({(z[i],z[j]) for z in table})==4
           for i,j in combinations(range(3),2))
assert len(table)<2**3
A=scale(F(1,2),add(I(3),scale(-1,outer(vec[0],vec[0]))))
B=scale(F(1,2),add(I(3),scale(-1,outer(vec[3],vec[3]))))
rho=scale(F(1,2),add(A,B))
assert mul(A,B)!=mul(B,A)
moment_checks=0
for w in product([F(-1,4),F(0),F(1,4),F(1,2)],repeat=3):
    v=sum(a*a for a in w)
    Ds=[]
    for word in table:
        Ds.append(total([scale(wi,add((A,B)[x],scale(-1,rho)))
                         for wi,x in zip(w,word)],3))
    assert total(Ds,3)==Z(3)
    assert scale(F(1,4),total([mul(D,D) for D in Ds],3)) == scale(
        v,add(scale(F(1,2),rho),scale(-1,mul(rho,rho))))
    moment_checks+=2
print(f"exact noncommuting rank-two and pairwise moment checks: {moment_checks}")

# Negative control: a variable-cutoff vector cannot simply replace the
# original signal in a test that need not commute with that projection.
psi=vec[3]
v=(F(4,5),-F(3,5),F(0))
P=outer(v,v)
cut=(F(3,5),F(0),F(0))
assert quad(psi,P)==0 and quad(cut,P)==F(144,625)
print("negative control: naive variable-truncation signal comparison fails")
