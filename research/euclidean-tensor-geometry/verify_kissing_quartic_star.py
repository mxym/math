#!/usr/bin/env python3
"""Polynomial identities for the all-orders cap-star maximum. Standard library only."""
from fractions import Fraction as F
from math import comb
def require(x):
    if not x: raise ArithmeticError("symbolic identity or inequality failed")
class P(dict):
    def __init__(self,v=0): super().__init__(v if isinstance(v,dict) else ({(0,0):F(v)} if v else {}))
    def __add__(self,o):
        r=P(self)
        for k,c in P(o).items():
            r[k]=r.get(k,0)+c
            if not r[k]:del r[k]
        return r
    __radd__=__add__
    def __mul__(self,o):
        r=P()
        for (a,b),c in self.items():
            for (i,j),z in P(o).items():r[(a+i,b+j)]=r.get((a+i,b+j),0)+c*z
        return P({k:v for k,v in r.items() if v})
    __rmul__=__mul__
    def __neg__(self):return self*(-1)
    def __sub__(self,o):return self+-P(o)
    def __rsub__(self,o):return P(o)+-self
    def __pow__(self,n):
        r=P(1)
        for i in range(n):r=r*self
        return r
    def dt(self):return P({(i,j-1):j*x for (i,j),x in self.items() if j})
def num(k,t):
    H=k+1+(k-1)*t*t;A=k+1+(k-1)*t;B=k+1-t
    N=2*(A**4+(k-1)*B**4)-k*H*(A*A+(k-1)*B*B)
    return H,N
n=P({(1,0):F(1)});t=P({(0,1):F(1)});k=n+3
H,N=num(k,t);V=2*H.dt()*N-N.dt()*H
b=[(n+4)*(3*n*n+14*n+7),(n+3)*(n+4)*(3*n+1),F(2,3)*(n+3)**2*(4*n+3),2*(n+3)**3]
B=sum(comb(3,i)*(1-t)**(3-i)*t**i*v for i,v in enumerate(b))
require(V==2*k*t*(k-1)*(k+1)*B)
require(all(c>0 for p in b for c in p.values()))
require(all(c>=0 for p in b for c in (p-k*(k+1)).values()))
H0,N0=num(k,P(0));require(N0==k*(k+1)*(k+2)*H0*H0)
H,N=num(2,t);V=2*H.dt()*N-N.dt()*H
require(V==48*t*(7*t*t-3))
def ev2(p,z):
    require(all(i==0 and j%2==0 for i,j in p));return sum(c*z**(j//2) for (i,j),c in p.items())
z=F(3,7);require(ev2(N,z)/(32*ev2(H,z)**2)==F(49,64))
print("PASS polynomial in k-3 and t; four positive cubic Bernstein coefficients; exceptional k=2 value 49/64")
