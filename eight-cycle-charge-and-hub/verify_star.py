#!/usr/bin/env python3
"""Finite signed-multiset certificates for the universal C8 hub-star bound."""
from itertools import combinations_with_replacement, permutations
P=1009
def rank(A):
    n=len(A); r=0
    for j in range(n):
        k=next((i for i in range(r,n) if A[i][j]),None)
        if k is None:
            continue
        A[r],A[k]=A[k],A[r]
        z=pow(A[r][j],-1,P)
        for i in range(r+1,n):
            if A[i][j]:
                g=A[i][j]*z%P
                for h in range(j,n):
                    A[i][h]=(A[i][h]-g*A[r][h])%P
        r+=1
    return r

def trace(u,w,q,c):
    word=sum(zip(u,(-x%q for x in w)),())
    result=0
    for start in range(q):
        x=start; factor=1
        for a in word:
            if a==0:
                if x!=0: break
            elif x==0:
                x=a
            elif x==(-a)%q:
                x=0
                factor=factor*c[a]%P
            else: break
        else:
            if x==start: result+=factor
    return result%P

def certified_defect(U,q):
    nz=tuple(i for i in U if i)
    if len(nz)==2 and nz[0]+nz[1]==q and nz[0]!=nz[1]:
        return 3
    if q%2==0:
        h=q//2
        if nz==(h,):return 1
        if nz==(h,h,h):return 3
        if len(nz)==3 and nz[1]==h and nz[0]+nz[2]==q:
            return 6
    return 0

for q in (11,12):
    c=[0]+[pow(43+2*i,i*i+1,P) for i in range(1,q)]
    count=0
    for U in combinations_with_replacement(range(q),4):
        if U[0]:continue
        I=sorted(set(permutations(U)))
        A=[[trace(u,w,q,c) for w in I] for u in I]
        expected=len(I)-certified_defect(U,q)
        assert rank(A)==expected,(q,U)
        count+=1
    print(q,count,'zero-containing multiset blocks passed')
