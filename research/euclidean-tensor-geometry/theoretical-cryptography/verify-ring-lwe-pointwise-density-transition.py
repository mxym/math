#!/usr/bin/env python3
"""Small arithmetic checks for the pointwise-profile proof."""
from cmath import exp as cxexp
from fractions import Fraction as F
from itertools import product
from math import pi
from random import Random

rng=Random(501)
def rot(x,q): return (-x[-1]%q,)+x[:-1]
def add(x,y,q): return tuple((a+b)%q for a,b in zip(x,y))
def dot(x,y,q): return sum(a*b for a,b in zip(x,y))%q
def mul(x,y,q):
    z=(0,)*len(x); v=x
    for a in y:
        z=add(z,tuple(a*b%q for b in v),q)
        v=rot(v,q)
    return z
def bar(x,q): return (x[0],)+tuple(-a%q for a in x[:0:-1])

# Exact ideal products after adjoining the even/odd coefficient blocks.
block=0
for q,d,g in ((3,4,(2,1,1,0)),(5,2,(3,1)),(9,2,(3,0))):
    J={mul(g,x,q) for x in product(range(q),repeat=d)}
    embed=tuple(a for v in g for a in (v,0))
    Jlarge={mul(embed,x,q) for x in product(range(q),repeat=2*d)}
    Jprod={tuple(t for pair in zip(a,b) for t in pair) for a,b in product(J,repeat=2)}
    assert Jlarge==Jprod
    assert len(J)>1 and all(len({x[j] for x in J})>1 for j in range(d))
    block+=len(Jlarge)

# One- and two-label Fourier orthogonality as an exact count.
relations=0
for q,d in ((3,2),(5,2),(9,2),(3,4)):
    R=list(product(range(q),repeat=d))
    for _ in range(110):
        s,t,v,w=[rng.choice(R) for k in range(4)]
        C=add(mul(bar(s,q),v,q),mul(bar(t,q),w,q),q)
        values=[(dot(mul(a,s,q),v,q)+dot(mul(a,t,q),w,q))%q for a in R]
        assert values==[dot(a,C,q) for a in R]
        if any(C):
            counts=[values.count(j) for j in set(values)]
            assert len(counts)>1 and len(set(counts))==1
        else:
            assert not any(values)
        relations+=1

origins=supremum=0
for q,d,k in ((3,2,1),(3,2,2),(5,2,1),(9,2,1)):
    R=list(product(range(q),repeat=d))
    for _ in range(26):
        A=[rng.choice(R) for i in range(k)]
        # Finite positive real Fourier coefficients selected for an
        # abstract nonnegative toy trigonometric polynomial.
        sample=[(tuple(rng.randrange(-q,q+1) for i in range(k*d)),F(1,rng.randrange(100,400))) for j in range(14)]
        sample += [(tuple(-v for v in x),w) for x,w in list(sample)]
        survive=[]
        for v,c in sample:
            O=(0,)*d; zero=True
            for i,a in enumerate(A):
                w=tuple(v[t]%q for t in range(i*d,(i+1)*d))
                O=add(O,mul(bar(a,q),w,q),q)
                zero&=not any(w)
            counts=[sum(dot(v[i*d:(i+1)*d],mul(a,s,q),q) for i,a in enumerate(A))%q for s in R]
            assert (not any(counts))==(not any(O))
            if not any(O) and not zero:
                survive.append((v,c))
            origins+=1
        m=sum(c for v,c in survive)
        for _ in range(17):
            Y=[rng.random() for j in range(k*d)]
            p=sum(float(c)*cxexp(2j*pi*sum(a*b for a,b in zip(Y,v))) for v,c in survive)
            assert abs(p)<=float(m)+1e-12 and abs(p.imag)<1e-12
            supremum+=1

print("PASS base ideal blocks / short relation phases / origin sectors / Fourier supremum:",
      block,relations,origins,supremum)
