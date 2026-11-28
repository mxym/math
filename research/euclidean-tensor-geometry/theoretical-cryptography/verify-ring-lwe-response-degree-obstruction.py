#!/usr/bin/env python3
"""Exact checks of the response-interaction norm on synthetic finite modules."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb

def parity(x):
    return x.bit_count()&1

def mul(u,v,d):
    out=0
    for i in range(d):
        if (v>>i)&1:
            out^=u<<i
    return out&((1<<d)-1)

class Chain:
    def __init__(self,d):
        self.d=d
        self.q=self.nr=1<<d
    def act(self,a,v):
        return mul(a,v,self.d)
    def ev(self,c,x):
        return 1-2*((mul(c,x,self.d)>>(self.d-1))&1)
    def right(self,c,a):
        return mul(c,a,self.d)

class Mat2:
    q=4
    nr=16
    def act(self,a,v):
        return parity(a&v)|(parity((a>>2)&v)<<1)
    def ev(self,c,x):
        return 1-2*parity(c&x)
    def right(self,c,a):
        return ((a&3) if c&1 else 0)^((a>>2) if c&2 else 0)

def zsum(xs):
    r=0
    for x in xs:
        r^=x
    return r

def orbit(C,xi):
    return {zsum(C.right(x,a) for x,a in zip(xi,cc))
            for cc in product(range(C.nr),repeat=len(xi))}

N0=N1=0
for C,dmax in [(Chain(1),3),(Chain(2),3),(Chain(3),3),(Mat2(),2)]:
    for r in range(1,dmax+1):
        for xis in product(range(1,C.q),repeat=r):
            counts=Counter()
            for coeff in product(range(C.nr),repeat=r):
                u=zsum(C.right(x,a) for x,a in zip(xis,coeff))
                counts[u]+=1
                for x,a in zip(xis,coeff):
                    for s in range(C.q):
                        assert C.ev(C.right(x,a),s)==C.ev(x,C.act(a,s))
                        N0+=1
            assert sum(counts.values())==C.nr**r
            assert len(set(counts.values()))==1
            assert set(counts)==orbit(C,xis)
            N1+=1

def conditional(C,z):
    p=[1+((x+1)*(z+3)+x*x)%11 for x in range(C.q)]
    return tuple(F(x,sum(p)) for x in p)

def nc(C,z,xi):
    return sum(p*C.ev(xi,x) for x,p in enumerate(conditional(C,z)))

# Direct input-character expectation on a fixed generated coefficient matrix,
# after averaging the independent finite noise fibers.
N2=0
for C in (Chain(2),Mat2()):
    for u in range(7):
        A=((u%C.nr,(u+1)%C.nr),((2*u+3)%C.nr,(u*u+3)%C.nr))
        for Z in product((0,1),repeat=2):
            for xi in product(range(C.q),repeat=2):
                noise=nc(C,Z[0],xi[0])*nc(C,Z[1],xi[1])
                for sep in product(range(C.q),repeat=2):
                    direct=0
                    for S in product(range(C.q),repeat=2):
                        signal=[zsum(C.act(a,s) for a,s in zip(row,S)) for row in A]
                        direct+=C.ev(sep[0],S[0])*C.ev(sep[1],S[1])*C.ev(xi[0],signal[0])*C.ev(xi[1],signal[1])
                    direct=F(direct,C.q**2)*noise
                    conj=tuple(zsum(C.right(xi[i],A[i][j]) for i in range(2)) for j in range(2))
                    assert direct==(noise if conj==sep else 0)
                    N2+=1

# Exact averaging of the finite fiber spectra and the full nilpotent-chain
# weight enumerator, for synthetically chosen public label probabilities.
N3=N4=0
for k in (1,2,3,4):
    C=Chain(k)
    w={x:(nc(C,0,x)**2+2*nc(C,1,x)**2)/3 for x in range(1,C.q)}
    W=[sum(ww for x,ww in w.items() if x%(1<<(k-j))==0) for j in range(k+1)]
    assert W[0]==0 and W[-1]<=C.q-1
    for r in (1,2,3):
        counts=[F(0)]*(k+1)
        for xi in product(range(1,C.q),repeat=r):
            j=max(k-(x&-x).bit_length()+1 for x in xi)
            weight=F(1)
            for x in xi:
                weight*=w[x]
            counts[j]+=weight
            N3+=1
        for j in range(1,k+1):
            assert counts[j]==W[j]**r-W[j-1]**r
        for n in (1,2,4):
            for a in range(1,k+1):
                aa=sum(counts[j]/2**(j*n) for j in range(a,k+1))
                bb=sum((W[j]**r-W[j-1]**r)/2**(j*n) for j in range(a,k+1))
                assert aa==bb
                N4+=1

# Check the conditional Fourier bound in the whole-element likelihood:
# norm of a single shifted full fiber does not depend on the translation.
N5=0
for C in (Chain(2),Chain(3),Mat2()):
    for z in (0,1):
        p=conditional(C,z)
        target=sum(x*x for x in p)*C.q-1
        for s in range(C.q):
            v=sum(sum(p[x^s]*C.ev(c,x) for x in range(C.q))**2
                  for c in range(1,C.q))
            assert v==target
            N5+=1

print("PASS: dual-action and uniform image identities =",N0,N1)
print("PASS: conditional input-character identities =",N2)
print("PASS: chain enumeration and shifted-fiber Parseval =",N3,N4,N5)
