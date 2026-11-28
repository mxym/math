#!/usr/bin/env python3
"""Exact scalar checks for the sharp heptagon constants. Standard library only."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
def iv(x,y=None):
    if isinstance(x,tuple):return x
    return (Q(x),Q(x if y is None else y))
def add(x,y):
    x,y=iv(x),iv(y);return x[0]+y[0],x[1]+y[1]
def neg(x):a,b=iv(x);return -b,-a
def sub(x,y):return add(x,neg(y))
def mul(x,y):
    e=[a*b for a in iv(x) for b in iv(y)];return min(e),max(e)
def div(x,y):
    a,b=iv(y);assert a*b>0
    return mul(x,(1/b,1/a))
def poly(x):return 8*x**3+4*x*x-4*x-1
def root(lo,hi):
    x,y=Q(lo,10**10),Q(hi,10**10)
    assert poly(x)*poly(y)<0;return x,y
a,b,c=[root(x,x+1)for x in (6234898018,-2225209340,-9009688680)]
r=div(sub(b,c),sub(a,c));s=div(sub(a,b),sub(a,c))
A=[add(sub(1,c),mul(r,sub(1,a))),add(sub(a,c),mul(r,sub(b,a))),r]
B=[add(sub(1,b),mul(s,sub(1,a))),add(sub(c,b),mul(s,sub(b,a))),s]
assert all(t[0]>0 and 2*t[0]>max(abs(v[0]),abs(v[1])) for t,v in zip(A,B))
w=div(sub(a,Q(1,2)),sub(a,c))
x=add(c,mul(w,sub(b,c)));z=add(b,mul(w,sub(a,b)))
assert 0<w[0]<=w[1]<1 and -1<x[0]<=x[1]<Q(-84,100) and Q(-1,2)<z[0]<=z[1]<Q(1,2)
def f(t):
    t2=mul(t,t);return mul(t2,sub(t2,Q(1,4)))
C=div(add(Q(3,4),mul(2,add(f(x),f(z)))),7)
assert Q(20085027,10**8)<C[0]<=C[1]<Q(20085029,10**8)
assert Q(84601073,10**8)<-x[1]<=-x[0]<Q(84601075,10**8)
pairs=[[(i,j)for i,j in combinations_with_replacement((2,3,4,5),2)if(i+j)%7==h]for h in range(7)]
assert max(map(len,pairs))==2
print("PASS: energy in (0.20085027,0.20085029); mean strength in (0.84601073,0.84601075); seven Fourier systems of height at most two.")
