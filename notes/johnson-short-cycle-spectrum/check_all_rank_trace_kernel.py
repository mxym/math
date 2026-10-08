#!/usr/bin/env python3
"""Exact trace-polynomial kernel for simultaneous Johnson actions.

No external packages, optimizer, or floating-point calculations.
1) Check the exact universal degree-six polynomial relation.
2) Check the induced equality of all k-subset orbital moments in sample n,k.
3) Independently verify full dimension floor(n/2)+1 of the all-rank
   class-function space by exact rational elimination on 2-cycle classes.
"""
from fractions import Fraction as Q
from math import comb
from transfer import moment

def poly_add(A,B,scale=1):
    n=max(len(A),len(B))
    return tuple((A[i] if i<len(A) else 0)+
                 scale*(B[i] if i<len(B) else 0) for i in range(n))

def poly_mul(A,B):
    C=[0]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        for j,b in enumerate(B):
            C[i+j]+=a*b
    return tuple(C)

def poly_pow(A,n):
    p=(1,)
    for _ in range(n):
        p=poly_mul(p,A)
    return p

def cycle_poly(types):
    out=(1,)
    for k in types:
        out=poly_mul(out,tuple(1 if j in (0,k) else 0
                                for j in range(k+1)))
    return out

def poly_relation(n):
    assert n>=6
    I=(1,)*n
    A=(4,)+(1,)*(n-4)
    T=(2,)+(1,)*(n-2)
    E=(3,3)+(1,)*(n-6)
    relation=poly_add(poly_add(tuple(5*x for x in cycle_poly(I)),
                               cycle_poly(A),9),
                      poly_add(tuple(-12*x for x in cycle_poly(T)),
                               cycle_poly(E),-2))
    assert set(relation)=={0},(n,relation)

def moment_relation(n,k):
    I=(n,)+(0,)*(k-1)
    A=(n-4,)+(0,)*(k-4)+(1,)+(0,)*0 if False else \
      tuple((n-4 if i==0 else 1 if i==3 else 0)
            for i in range(k))
    T=tuple((n-2 if i==0 else 1 if i==1 else 0)
            for i in range(k))
    E=tuple((n-6 if i==0 else 2 if i==2 else 0)
            for i in range(k))
    # For k<4 or k<3 the unrecorded larger cycles are correctly
    # absorbed by the short-cycle transfer evaluator.
    A=tuple((n-4 if i==0 else 1 if i==3 else 0)
            for i in range(k))
    E=tuple((n-6 if i==0 else 2 if i==2 else 0)
            for i in range(k))
    def proper(t):
        rem=n-sum((i+1)*z for i,z in enumerate(t))
        assert rem==0 or rem>=k+1
        return moment(n,k,t)
    v1,v2,v3,v4=map(proper,(I,A,T,E))
    assert all(5*v1[j]+9*v2[j]==12*v3[j]+2*v4[j]
               for j in range(k+1)),(n,k)

def rank(rows):
    m=[[Q(x) for x in row] for row in rows]
    height=len(m);width=len(m[0]);pivots=0
    for col in range(width):
        first=next((i for i in range(pivots,height) if m[i][col]),None)
        if first is None:continue
        m[pivots],m[first]=m[first],m[pivots]
        a=m[pivots][col]
        m[pivots]=[v/a for v in m[pivots]]
        for i in range(pivots+1,height):
            a=m[i][col]
            if a:
                m[i]=[m[i][j]-a*m[pivots][j] for j in range(width)]
        pivots+=1
        if pivots==height:break
    return pivots

def full_rank(n):
    d=n//2
    arr=[]
    for r in range(d+1):
        p=(2,)*r+(1,)*(n-2*r)
        arr.append(cycle_poly(p)[:d+1])
    assert rank(arr)==d+1

def main():
    for n in range(6,101):
        poly_relation(n)
    for n in range(6,22):
        for k in range(1,n+1):
            moment_relation(n,k)
    for n in range(6,31):
        full_rank(n)
    print('PASS degree-six polynomial identity for n=6..100')
    print('PASS every orbital k=1..n for n=6..21')
    print('PASS exact full trace-rank floor(n/2)+1 for n=6..30')
    print('ALL-RANK TRACE-KERNEL TESTS PASSED')

if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

if __name__=='__main__':
    main()
