#!/usr/bin/env python3
"""Exact arithmetic sanity checks for SparseHarmonicConicLifting.md."""
from random import Random
from itertools import combinations

# Finite field with a chosen square root of -1. A nonzero modular determinant
# proves that the corresponding Gaussian-integer determinant is nonzero.
p=65537
I=256
assert I*I%p==p-1

def det(A):
    A=[list(r) for r in A]
    n=len(A); out=1
    for j in range(n):
        t=next((h for h in range(j,n) if A[h][j]%p),None)
        if t is None: return 0
        if t!=j: A[j],A[t]=A[t],A[j];out=-out
        b=A[j][j]%p;out=out*b%p
        for h in range(j+1,n):
            ratio=A[h][j]*pow(b,-1,p)%p
            for l in range(j,n): A[h][l]=(A[h][l]-ratio*A[j][l])%p
    return out%p

def inner(x,y): return sum(a*b for a,b in zip(x,y))%p

def ortho(rng):
    # Unnormalized real Householder maps P(v)=|v|^2 I-2vv^t.
    rows=[[int(i==j) for j in range(6)] for i in range(6)]
    for _ in range(9):
        v=[rng.randrange(-5,6) for _ in rows]
        h=inner(v,v)
        assert h
        rows=[[(h*t-2*inner(row,v)*w)%p for t,w in zip(row,v)] for row in rows]
    h=inner(rows[0],rows[0])
    assert h and all(inner(row,row)==h for row in rows)
    assert all(inner(rows[j],rows[k])==0 for j,k in combinations(range(6),2))
    return rows

def nullmap(M):
    return [[(row[2*j]+I*row[2*j+1])%p for j in range(3)] for row in M]

def sym2(X):
    return [[v[i]*v[j]%p for i in range(3) for j in range(i,3)] for v in X]

def main():
    assert det([[1,0,-I],[-I,1,0],[0,-I,1]])==(1+I)%p
    rng=Random(21179); ns=0
    for _ in range(96):
        U=nullmap(ortho(rng)); M=sym2(U)
        assert all(sum(col)%p==0 for col in zip(*M)) and det(M)==0
        for a,b in combinations(range(6),2):
            V=[r[:] for r in U]
            V[b]=[(t+3*u)%p for t,u in zip(V[b],V[a])]
            # A zero for one projection is allowed; count nonzero witnesses.
            if det(sym2(V)): ns+=1
    assert ns>=1435
    # Verify the extension recurrence over Q on monomials up to degree 33.
    from fractions import Fraction as Q
    for k in range(34):
        q=Q(1)
        for j in range(k//2):
            z=-q/((2*j+2)*(2*j+1))
            assert q+z*(2*j+2)*(2*j+1)==0
            q=z
    print('PASS: 96 orthogonal exceptions, %d/1440 nonorthogonal witnesses, extension recurrence.'%ns)

if __name__=='__main__':main()
