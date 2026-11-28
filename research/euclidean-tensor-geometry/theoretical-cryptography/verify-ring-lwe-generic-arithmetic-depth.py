"""Finite root-bound and local-ring checks for the generic arithmetic note.

No files, services, explicit instances or likelihood optimizers are used.
"""
from fractions import Fraction
from itertools import product
from random import Random

rng=Random(74403)
def add(a,b,q):
    return tuple((x+y)%q for x,y in zip(a,b))
def mult(a,b,q):
    x,y=a;u,v=b
    return ((x*u-y*v)%q,(x*v+y*u)%q)
def peval(C,x,q):
    v=(0,0)
    for c in C[::-1]:
        v=add(c,mult(x,v,q),q)
    return v
def pvaluation(C):
    return min(0 if v%3 else 1 if v%9 else 2 for c in C for v in c)
def poly_product(C,D):
    U=[(0,0)]*(len(C)+len(D)-1)
    for i,c in enumerate(C):
        for j,d in enumerate(D):
            U[i+j]=add(U[i+j],mult(c,d,9),9)
    return U

# Over Z/9[x]/(x^2+1), x^2+1 is irreducible modulo 3 and the
# reduction of each nonzero polynomial after stripping 3-adic valuation
# detects all of its possible ring roots.
Z9=list(product(range(9),repeat=2))
Z3=list(product(range(3),repeat=2))
roots=valuation=units=0
for d in range(1,7):
    for v in (0,1):
        for _ in range(130):
            Q=[tuple(rng.randrange(9//(3**v)) for _ in range(2)) for _ in range(d+1)]
            if all(x%3==0 for a in Q for x in a): continue
            P=[tuple(x*3**v%9 for x in a) for a in Q]
            assert pvaluation(P)==v
            W=[tuple(x%3 for x in a) for a in Q]
            assert sum(peval(W,z,3)==(0,0) for z in Z3)<=d
            for z in Z9:
                if peval(P,z,9)==(0,0):
                    assert peval(W,tuple(x%3 for x in z),3)==(0,0)
                    roots+=1
            D=[rng.choice(Z9) for _ in range(1+rng.randrange(4))]
            if pvaluation(D)==0:
                assert pvaluation(poly_product(P,D))==v
                valuation+=1
for a in Z9:
    inv=[b for b in Z9 if mult(a,b,9)==(1,0)]
    assert len(inv)==int(any(x%3 for x in a))
    units+=len(inv)

# The atom hypothesis need not make variables independent.
# A correlated positive weight table in [1,3] has point conditionals <=3/p.
root_tests=0
for p,n in ((5,3),(7,2),(11,2)):
    V=list(product(range(p),repeat=n))
    for _ in range(180):
        weights=[rng.randint(1,3) for x in V]
        for i in range(n):
            row={}
            for x,w in zip(V,weights):
                y=x[:i]+x[i+1:]
                row.setdefault(y,[]).append(w)
            assert all(p*max(a)<=3*sum(a) for a in row.values())
        a=[rng.randrange(p) for _ in range(n)]
        b=rng.randrange(p)
        e=rng.randrange(p)
        # max degree 2; a high-degree or identically zero function is not
        # needed to test this finite comparison.
        if not any(a) and not b and not e: continue
        degree=2 if b else int(any(a))
        numerator=sum(w for x,w in zip(V,weights)
                      if (sum(k*v for k,v in zip(a,x))+b*x[0]*x[-1]+e)%p==0)
        assert Fraction(numerator,sum(weights))<=Fraction(3*degree,p)
        root_tests+=1

# Bayes direction and CRT projection in a tiny finite instance.
bayes=0
for q in (3,9):
    V=list(product(range(q),repeat=2))
    b=Fraction(1,9)
    c=(1-b)**2
    C=(1+(q-1)*b)**2
    def likelihood(s,a,y):
        v=mult(s,a,q)
        out=Fraction(1)
        for u,x in zip(v,y):
            out*=1+b*(q*int(u==x)-1)
        return out
    for _ in range(90):
        s,y=rng.choices(V,k=2)
        w=[likelihood(s,a,y) for a in V]
        assert min(w)>=c and max(w)<=C
        total=sum(w)
        assert max(w)/total<=C/(c*len(V))
        mass={}
        p=3
        for a,w0 in zip(V,w):
            k=tuple(x%p for x in a)
            mass[k]=mass.get(k,0)+w0
        assert max(mass.values())/total<=C/(c*p*p)
        bayes+=1
print("PASS: local roots, primitive products, units, dependent root tables, Bayes rows:",
      roots,valuation,units,root_tests,bayes)
