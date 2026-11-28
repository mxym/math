#!/usr/bin/env python3
"""Exact small-matrix checks of the rank budget and affine-slice identity."""
from itertools import combinations, permutations, product
from random import Random
from math import prod


def matrank(A,p):
    R={}
    for v in A:
        a=list(v)
        for j,b in enumerate(a):
            b=a[j]
            if not b:
                continue
            if j not in R:
                R[j]=tuple(x*pow(b,-1,p)%p for x in a)
                break
            a=[(x-b*y)%p for x,y in zip(a,R[j])]
    return len(R)


def linearcombo(ms,z,p):
    n=len(ms[0])
    return tuple(tuple(sum(a*M[i][j] for a,M in zip(z,ms))%p
                       for j in range(n)) for i in range(n))


def bipair(M,x,y,p):
    return sum(M[i][j]*x[i]*y[j] for i in range(len(M))
               for j in range(len(M)))%p


def restrict(ms,B,p):
    return tuple(tuple(tuple(bipair(M,x,y,p) for y in B) for x in B) for M in ms)


def expand(B,u,p):
    return tuple(sum(a*b[i] for a,b in zip(u,B))%p for i in range(len(B[0])))


def null_basis(M,p):
    n=len(M)
    B=[]
    for v in product(range(p),repeat=n):
        if all(sum(a*b for a,b in zip(r,v))%p==0 for r in M) and matrank(B+[v],p)>len(B):
            B.append(v)
    assert len(B)==n-matrank(M,p)
    return B


def true_minor(ms,I,J,p):
    m=len(ms)
    out={}
    for perm in permutations(J):
        s=(-1)**sum(a>b for i,a in enumerate(perm) for b in perm[i+1:])
        lists=tuple(tuple((u,M[i][j]) for u,M in enumerate(ms) if M[i][j])
                    for i,j in zip(I,perm))
        for contrib in product(*lists):
            term=[0]*m
            k=s
            for u,v in contrib:
                term[u]+=1
                k=k*v%p
            term=tuple(term)
            out[term]=(out.get(term,0)+k)%p
    return any(out.values())


def generic_rank(ms,p):
    n=len(ms[0])
    for d in range(n,0,-1):
        choices=tuple(combinations(range(n),d))
        if any(true_minor(ms,I,J,p) for I,J in product(choices,repeat=2)):
            return d
    return 0


def matrix_tests(R):
    counts=[0]*4
    for p in (2,3,5):
        for n in range(1,5):
            for _ in range(36):
                m=R.randrange(1,4)
                ms=[]
                alt=R.randrange(2)==0
                for __ in range(m):
                    A=[[0]*n for __ in range(n)]
                    for i in range(n):
                        for j in range(i,n):
                            A[i][j]=0 if i==j and alt else R.randrange(p)
                            A[j][i]=(-1 if alt else 1)*A[i][j]%p
                    ms.append(tuple(map(tuple,A)))
                r=generic_rank(ms,p)
                ranks=[matrank(linearcombo(ms,z,p),p) for z in product(range(p),repeat=m)]
                assert sum(ranks)*p>=len(ranks)*(p-1)*r
                counts[0]+=1
                counts[1]+=len(ranks)
                for i in range(m):
                    K=null_basis(ms[i],p)
                    r2=generic_rank(restrict(ms,K,p),p)
                    assert r>=matrank(ms[i],p)+r2
                    counts[2]+=1
                B=[tuple(int(i==j) for j in range(n)) for i in range(n)]
                while True:
                    selected=next((M for M in restrict(ms,B,p) if any(map(any,M))),None)
                    if selected is None:
                        break
                    K=null_basis(selected,p)
                    B=[expand(B,u,p) for u in K]
                assert n-len(B)<=r
                assert all(not any(map(any,M)) for M in restrict(ms,B,p))
                counts[3]+=1
    return counts


def diagonal_tests():
    total=0
    for p,m in product((2,3,5),(1,2,3)):
        projective=[u for u in product(range(p),repeat=m)
                    if any(u) and next(c for c in u if c)==1]
        assert len(projective)==(p**m-1)//(p-1)
        for x in product(range(p),repeat=m):
            if any(x):
                assert sum(sum(a*b for a,b in zip(x,u))%p!=0
                           for u in projective)==p**(m-1)
                total+=1
    return total


def fq4_mul(x,y):
    z=0
    for _ in range(2):
        if y&1:
            z^=x
        y>>=1
        x<<=1
        if x&4:
            x^=7
    return z


def slices():
    # In GF(4), square terms are additive but are not generally GF(4)-linear.
    mult=fq4_mul
    count=0
    for z,k,u,w,t,s in product(range(4),repeat=6):
        # U is the last two coordinates in Q(z,y1,y2)=z*y1+k*y2^2+y1.
        def f(a,b):
            return mult(z,a)^mult(k,mult(b,b))^a
        assert f(u^t,w^s)==f(u,w)^f(t,s)
        count+=1
    assert mult(2,2)!=2
    return count


def main():
    R=Random(927446)
    print("PASS rank spaces / specializations / radical tests / greedy / projective / GF4 slices:",
          *matrix_tests(R),diagonal_tests(),slices())


if __name__=="__main__":
    main()
