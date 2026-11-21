#!/usr/bin/env python3
"""Exact terminal search for size-three EACs at 2^a,2*3^a; standard library."""
from math import gcd,isqrt
def ck(x,s):
    if not x:raise ArithmeticError(s)
def primes(t):
    a=bytearray([1])*(t+1)
    if t>=0:a[0]=0
    if t>=1:a[1]=0
    for p in range(2,isqrt(t)+1):
        if a[p]:a[p*p:t+1:p]=bytes((t-p*p)//p+1)
    return [p for p in range(2,t+1) if a[p]]
ns=[2**a for a in range(2,26)]+[2*3**a for a in range(1,16)]
ps=primes(isqrt(max(ns))+1)
def fac(n):
    a={};v=n
    for p in ps:
        if p*p>v:break
        while v%p==0:a[p]=a.get(p,0)+1;v//=p
    if v>1:a[v]=1
    ck(n==__import__('math').prod(p**a[p] for p in a),'factorization')
    return a
def strongly(C,A):
    for s in C:
        a={s}
        while True:
            b=a|set().union(*(set(A[t]) for t in a))
            if b==a:break
            a=b
        if a!=C:return False
    return True
def sweep(n):
    count=0;trial=0;out=set()
    for q in ps:
        if q*q>=n:break
        if q==2 or gcd(q,n)>1:continue
        W=q*q
        while W<n:
            p=n-W;W*=q
            if p<3 or p==q or max(p,q)>(n-3)//3 or gcd(p,n)>1:continue
            if fac(p)!={p:1}:continue
            count+=1;a=fac(n-q);other=set(a)-{p}
            if len(other)!=1:continue
            r=other.pop()
            if r<=max(p,q) or r>(n-3)//3 or gcd(r,n)>1:continue
            trial+=1;C={p,q,r};A={v:fac(n-v) for v in C}
            if all(set(row)<=C and sum(row.values())>=2 for row in A.values()) and strongly(C,A):
                out.add(tuple(sorted(C)))
    return count,trial,out
ck(4*8192*27>5*55**3 and 57**6<2*55**6,'dyadic threshold')
ck(3**8*4>27**3 and 19**6<3*18**6,'ternary threshold')
tot=cnt=0
for n in ns:
    a,b,out=sweep(n);ck(not out,(n,out));tot+=a;cnt+=b
print(len(ns),'centers;',tot,'pure-row candidates;',cnt,'terminal triple checks; none')
