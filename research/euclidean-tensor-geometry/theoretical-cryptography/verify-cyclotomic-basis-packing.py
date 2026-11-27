#!/usr/bin/env python3
"""Exact certificates for disjoint integral cyclotomic bases and contraction."""
from itertools import product
from math import prod

CERTIFICATES = {
    7: ((953, 1000),
        [0, 1, 4, 5, 6, 7, 9, 10, 11, 14, 18, 21, 24, 26,
         29, 30, 31, 32, 34, 35, 37, 38, 42, 48, 50, 52, 53, 54,
         55, 58, 59, 68, 71, 72, 75, 76, 78, 79, 80, 83, 85, 89,
         91, 92, 95, 97, 98, 102],
        [2, 3, 8, 12, 13, 15, 16, 17, 19, 20, 22, 23, 25, 27,
         28, 33, 36, 39, 40, 41, 43, 44, 45, 46, 47, 49, 51, 56,
         57, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 73, 74, 77,
         81, 84, 87, 94, 99, 100]),
    11: ((99, 100),
        [0, 1, 2, 3, 4, 8, 9, 12, 13, 15, 16, 20, 21, 23,
         24, 27, 28, 29, 30, 31, 34, 38, 42, 46, 47, 50, 51, 52,
         59, 61, 62, 65, 69, 71, 72, 73, 74, 80, 81, 85, 86, 88,
         89, 90, 91, 93, 95, 98, 99, 100, 101, 104, 105, 106, 108, 109,
         110, 111, 113, 115, 116, 118, 119, 121, 123, 124, 125, 131, 132, 136,
         137, 142, 143, 147, 149, 150, 151, 152, 153, 162],
        [5, 6, 7, 10, 11, 14, 17, 18, 19, 22, 25, 26, 32, 33,
         35, 36, 37, 39, 40, 41, 43, 44, 45, 48, 49, 53, 54, 55,
         56, 57, 58, 60, 63, 64, 66, 67, 68, 70, 75, 76, 77, 78,
         79, 82, 83, 84, 87, 92, 94, 96, 97, 102, 103, 107, 112, 114,
         117, 120, 122, 126, 127, 128, 129, 130, 133, 134, 135, 138, 139, 140,
         141, 144, 145, 146, 148, 154, 155, 156, 157, 161]),
    13: ((499, 500),
        [1, 2, 3, 4, 6, 9, 11, 17, 19, 26, 28, 29, 33, 34,
         37, 39, 40, 43, 44, 45, 46, 49, 50, 51, 54, 57, 60, 63,
         64, 66, 67, 70, 72, 74, 75, 76, 77, 78, 81, 85, 86, 92,
         95, 96, 97, 98, 99, 101, 102, 103, 104, 106, 109, 113, 115, 116,
         117, 118, 121, 124, 126, 127, 130, 134, 137, 138, 140, 143, 144, 145,
         146, 147, 148, 152, 153, 154, 155, 156, 159, 161, 162, 168, 170, 171,
         172, 175, 177, 179, 183, 185, 186, 188, 189, 190, 191, 194],
        [0, 5, 7, 8, 10, 12, 13, 14, 15, 16, 18, 20, 21, 22,
         23, 24, 25, 27, 30, 31, 32, 35, 36, 38, 41, 42, 47, 48,
         52, 53, 55, 56, 58, 59, 61, 62, 65, 68, 69, 71, 73, 79,
         80, 82, 83, 84, 87, 88, 89, 90, 91, 93, 94, 100, 105, 107,
         108, 110, 111, 112, 114, 119, 120, 122, 123, 125, 128, 129, 131, 132,
         133, 135, 136, 139, 141, 142, 149, 150, 151, 157, 158, 160, 163, 164,
         166, 167, 169, 173, 174, 176, 178, 180, 181, 182, 187, 192]),
}


def cell(s, r):
    i,u=divmod(s,5*r)
    j,k=divmod(u,r)
    return i,j,k


def local(p,a,b):
    # Coordinate a in the selected unit basis of local root b.
    return -1 if b==p-1 else int(a==b)


def basis_matrix(r, indices):
    sizes=(3,5,r)
    rr=list(product(*(range(p-1) for p in sizes)))
    cc=[cell(s,r) for s in indices]
    return [[prod(local(p,i,j) for p,i,j in zip(sizes,a,b)) for b in cc]
            for a in rr]


def bareiss(M, positive=False):
    B=[list(row) for row in M]
    n=len(B)
    assert all(len(row)==n for row in B)
    prev=1
    sgn=1
    pivots=[]
    for k in range(n):
        if positive:
            # With no pivoting, these are successive leading minors.
            assert B[k][k]>0
        elif B[k][k]==0:
            i=next((i for i in range(k+1,n) if B[i][k]),None)
            if i is None:
                return 0,pivots
            B[k],B[i]=B[i],B[k]
            sgn=-sgn
        current=B[k][k]
        pivots.append(current)
        if k==n-1:
            return current*sgn,pivots
        for i in range(k+1,n):
            for j in range(k+1,n):
                num=B[i][j]*current-B[i][k]*B[k][j]
                q,a=divmod(num,prev)
                assert a==0
                B[i][j]=q
            B[i][k]=0
        prev=current
    return 1,pivots


def scaled_gram(r, indices):
    sizes=(3,5,r)
    cc=[cell(s,r) for s in indices]
    return [[prod(p*int(i==j)-1 for p,i,j in zip(sizes,a,b))
             for b in cc] for a in cc]


def reference_gram(r, M):
    # Independently, construct the normalized reference Gram in its unit basis
    # and calculate M^T G M. Returns the same integer scaling 15r.
    sizes=(3,5,r)
    rr=list(product(*(range(p-1) for p in sizes)))
    G=[[prod(p*int(i==j)-1 for p,i,j in zip(sizes,a,b))
        for b in rr] for a in rr]
    cols=list(zip(*M))
    tmp=[[sum(x*y for x,y in zip(a,b)) for b in cols] for a in G]
    tc=list(zip(*tmp))
    return [[sum(x*y for x,y in zip(a,b)) for b in tc] for a in cols]


expected={7:(1,-1),11:(-1,1),13:(1,-1)}
count=0
for r,((num,den),S,T) in CERTIFICATES.items():
    n=8*(r-1)
    m=15*r
    assert 2*n<m
    assert len(S)==len(T)==n
    assert sorted(set(S))==S and sorted(set(T))==T
    assert all(0<=u<m for u in S+T) and not set(S)&set(T)
    A=basis_matrix(r,S)
    B=basis_matrix(r,T)
    da,_=bareiss(A)
    db,_=bareiss(B)
    assert (da,db)==expected[r]
    G=scaled_gram(r,S)
    assert G==reference_gram(r,A)
    D=[[m*num*int(i==j)-den*G[i][j] for j in range(n)] for i in range(n)]
    _,pivots=bareiss(D,positive=True)
    assert len(pivots)==n
    count+=n
    print(f"PASS {m}: dimension {n}, determinants {da:+d},{db:+d}, "
          f"contracting squared norm strictly below {num}/{den}")
print("PASS exact positive leading minors",count)
