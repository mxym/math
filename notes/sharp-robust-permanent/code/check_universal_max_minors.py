#!/usr/bin/env python3
"""A universal, exact, solver-free determinant formula for Sn k-subset atom TV.

Finite max/min over integer minors, NOT an LP, MILP or floating heuristic.
The mathematical proof (circuit reduction plus full-rank determinant) is
in companion manuscript. Relies only on standard-library integer operations.
"""
from itertools import combinations
from math import comb,prod
from fractions import Fraction
from check_all_k_orbital_compression import from_short_cycles


def profiles(n,m):
    def rec(j,remain,current):
        if j==m+1:
            if remain==0 or remain>=m+1:
                yield tuple(current)
            return
        for c in range(remain//j+1):
            current.append(c)
            yield from rec(j+1,remain-j*c,current)
            current.pop()
    return list(rec(1,n,[]))


def column(n,m,t):
    return (1,)+tuple(from_short_cycles(n,m,t)[:m])


def det_int(M):
    size=len(M)
    assert all(len(row)==size for row in M)
    if size==0:return 1
    A=[list(map(int,row)) for row in M]
    sign=1
    div=1
    for p in range(size-1):
        if A[p][p]==0:
            swap=next((j for j in range(p+1,size) if A[j][p]),None)
            if swap is None:return 0
            A[p],A[swap]=A[swap],A[p]
            sign=-sign
        pivot=A[p][p]
        for i in range(p+1,size):
            for j in range(p+1,size):
                z=A[i][j]*pivot-A[i][p]*A[p][j]
                assert z%div==0,(size,p,i,j,z,div)
                A[i][j]=z//div
        for i in range(p+1,size):A[i][p]=0
        div=pivot
    return sign*A[-1][-1]


def fullrank_witness(n,m):
    cols=[]
    for j in range(m):
        counts=[0]*m
        counts[0]=j
        cols.append(tuple(column(n,m,tuple(counts))))
    identity=(n,)+(0,)*(m-1)
    cols.append(tuple(column(n,m,identity)))
    M=[[cols[j][i] for j in range(m+1)] for i in range(m+1)]
    actual=det_int(M)
    expect=(-1)**m*prod(comb(n-2*r,m-r) for r in range(m))
    assert actual==expect,(n,m,actual,expect)
    return actual


def exact_value(n,k):
    assert n>=1 and 0<=k<=n
    if n==1:return Fraction(0),None,0
    m=min(k,n-k)
    if m==0:return Fraction(1),None,0
    assert n>=2*m
    fullrank_witness(n,m)
    T=profiles(n,m)
    identity=(n,)+(0,)*(m-1)
    assert identity in T
    others=[t for t in T if t!=identity]
    if len(others)<m+1:
        return Fraction(0),None,0
    identity_col=column(n,m,identity)
    cols={t:column(n,m,t) for t in T}
    best=Fraction(0)
    witness=None
    tested=0
    for ts in combinations(others,m+1):
        sub=(identity,)+ts
        vals=[cols[t] for t in sub]
        cof=[]
        for j in range(m+2):
            mat=[[vals[l][i] for l in range(m+2) if l!=j] for i in range(m+1)]
            cof.append((-1)**j*det_int(mat))
        total=sum(abs(v) for v in cof)
        if total:
            assert all(sum(cof[j]*vals[j][i] for j in range(m+2))==0
                       for i in range(m+1)),('kernel-failure',n,m,sub,cof)
            value=Fraction(2*abs(cof[0]),total)
            if value>best:
                best=value
                witness=(sub,cof)
        tested+=1
    return best,witness,tested


def main():
    for m in range(1,10):
        for n in (2*m,2*m+1,2*m+5):
            d=fullrank_witness(n,m)
            print('FULL RANK',n,m,'det',d,flush=True)
    cases=[(2,1),(3,1),(4,1),(5,1),(4,2),(5,2),(6,2),(7,2),
           (6,3),(7,3),(8,3),(9,3),(10,3),(8,4),(9,4)]
    want={(2,1):Fraction(0),(3,1):Fraction(1,3),(4,1):Fraction(1,2),
          (5,1):Fraction(3,5),(4,2):Fraction(1,3),
          (5,2):Fraction(1,3),(6,2):Fraction(2,5),
          (7,2):Fraction(23,55),(6,3):Fraction(5,14),
          (7,3):Fraction(5,14),(8,3):Fraction(89,244),
          (9,3):Fraction(259,691),(10,3):Fraction(368,935),
          (8,4):Fraction(5,14),(9,4):Fraction(5,14)}
    for n,k in cases:
        result,witness,count=exact_value(n,k)
        print('EXACT MAX-MINORS',n,k,'=',result,'tuples',count,flush=True)
        assert result==want[n,k],(n,k,result,want[n,k])
        if witness:
            assert len(witness[0])==min(k,n-k)+2
    assert exact_value(8,5)[0]==Fraction(89,244)
    assert exact_value(5,0)[0]==1
    assert exact_value(1,0)[0]==0
    print('UNIFIED DETERMINANT FORMULA FINITE REPLAY PASSED')


if __name__=='__main__':
    import sys
    if len(sys.argv)==3:
        n,k=map(int,sys.argv[1:])
        v,w,num=exact_value(n,k)
        print('EXACT RATIONAL OPTIMUM C_{%s,%s} = %s'%(n,k,v))
        print('MAXIMAL-MINOR TUPLES TESTED:',num)
        if w:
            print('ATTAINING PROFILES:',w[0])
            print('ATTAINING SIGNED INTEGER MINORS:',w[1])
    elif len(sys.argv)==1:
        main()
    else:
        raise SystemExit('Usage: python check_universal_max_minors.py [n k]')
