#!/usr/bin/env python3
"""Independent nonbinary coefficient enumeration, interpolation and product laws."""
from itertools import product, permutations
from fractions import Fraction as F
from math import prod
import random


def stage(p, alph, anchors, examples, exhaustive=True):
    points = list(product(*alph))
    exponents = list(product(*(range(len(a)) for a in alph)))
    shifted = [[prod(pow((x[i]-anchors[i]) % p,j,p) for i,j in enumerate(e))%p
                for e in exponents] for x in points]
    fixed=[]
    for base,end in examples:
        def density(x,t):
            return prod(t[i]/len(alph[i]) + (1-t[i])*(x[i]==anchors[i])
                        for i in range(len(x)))
        mu=[density(x,base) for x in points]
        nu=[density(x,end) for x in points]
        rr=[a/b for a,b in zip(end,base)]
        active={i for i,r in enumerate(rr) if r<1}
        bound=[prod(sorted(rr)[:d]) for d in range(sum(len(a)-1 for a in alph)+1)]
        fixed.append((mu,nu,active,bound,rr))
    rng = random.Random(20261127+p)
    polys=product(range(p),repeat=len(exponents)) if exhaustive else (
        tuple(rng.randrange(p) if sum(e)<=d else 0 for e in exponents)
        for d in range(sum(len(a)-1 for a in alph)+1) for _ in range(110))
    tests=equal=0
    for cs in polys:
        terms=[(e,c) for e,c in zip(exponents,cs) if c]
        if not terms: continue
        d=max(sum(e) for e,c in terms)
        support=[k for k,row in enumerate(shifted)
                 if sum(x*y for x,y in zip(row,cs)) % p]
        assert support
        for weights,after,active,bound,r in fixed:
            m0=sum(weights[j] for j in support)
            m1=sum(after[j] for j in support)
            factor=bound[d]
            assert m1>=factor*m0
            if d>=len(active):
                criterion=all(all(points[j][i]!=anchors[i] for i in active) for j in support)
            else:
                e,c=terms[0]
                K={i for i,v in enumerate(e) if v}
                criterion=(len(terms)==1 and len(K)==d and K<=active
                           and prod(r[i] for i in K)==factor)
            assert (m1==factor*m0)==criterion
            tests+=1
            equal+=criterion
    return tests,equal


def vandermonde(p, alph):
    # Direct closed-form field reductions, plus arbitrary coordinate orders
    # on a mixed grid.  No Gaussian or Gram construction is used.
    points=list(product(*alph))
    D=sum(len(a)-1 for a in alph)
    bases=[list(permutations(a)) for a in alph]
    def weight(a,x):
        return pow(prod((x-y)%p for y in a if y!=x)%p,-1,p)
    for e in product(*(range(len(a)+1) for a in alph)):
        if sum(e)<D:
            s=sum(prod(weight(a,x[i])*pow(x[i],e[i],p) for i,a in enumerate(alph))
                  for x in points)
            assert s%p==0
    counts=0
    for i in range(1,p):
        for j in range(p):
            for k in range(p):
                for l in range(p):
                    S=[x for x in points if (i*x[0]*x[1]+j*x[0]+k*x[1]+l)%p]
                    if not S: continue
                    for ordering in product(*bases):
                        total=sum(sum(a.index(v) for a,v in zip(ordering,x)) for x in S)
                        assert (D-2)*len(S)<=2*total<=(D+2)*len(S)
                        counts+=1
    return counts


def main():
    a = stage(3, ((0,1,2),(0,1,2)), (1,2),
              [((F(1),F(4,5)),(F(3,4),F(3,5))),
               ((F(3,4),F(3,5)),(F(3,4),F(1,2)))])
    b = stage(5, ((0,2),(1,2,4)), (2,1),
              [((F(1),F(2,3)),(F(5,9),F(2,3))),
               ((F(1),F(1)),(F(5,7),F(3,7)))])
    c = stage(7, ((0,2),(1,2,4),(0,3,5)), (2,1,3),
              [((F(1),F(1),F(5,7)),(F(5,7),F(5,7),F(5,7))),
               ((F(1),F(1),F(1)),(F(3,5),F(3,5),F(4,5)))], exhaustive=False)
    print(f'nonbinary coefficient checks (GF3 uniform-size, GF5 heterogeneous, GF7 sampled 3D): {a}, {b}, {c} (comparisons, equalities)')
    q=vandermonde(5,((0,2),(1,2,4)))
    print(f'weighted top-moment and direct support rank checks in all orders: {q}')
    # The claimed sharpness for d>number of coordinates uses a repeated
    # anchor factor; avoiding the anchor is all that matters to the law.
    for d in range(3,6):
        exponents=(min(2,d-1), d-min(2,d-1))
        assert all(0<i<4 for i in exponents)
        support=[(x,y) for x,y in product(range(4),repeat=2)
                 if (x**exponents[0]*y**exponents[1])%5]
        assert len(support)==9 and all(x and y for x,y in support)
    # A rational mixed-size grid illustrates the tied optimum and tests
    # strictness when two monomials overlap over a characteristic-zero field.
    grid=((F(3,2),F(-1,2)), (F(0),F(2,5),F(3)))
    a0,a1=grid[0][0],grid[1][0]
    mu=(F(1),F(2,3)); nue=(F(3,4),F(1,2))
    def nz(f, law):
        return sum(prod(t/len(a)+(1-t)*(v==z) for t,a,z,v in zip(law,grid,(a0,a1),x))
                   for x in product(*grid) if f(*x))
    one=lambda x,y:x-a0
    both=lambda x,y:x-a0+y-a1
    assert nz(one,nue)==F(3,4)*nz(one,mu)
    assert nz(both,nue)>F(3,4)*nz(both,mu)
    print('PASS reduced-degree nonbinary support, interpolation and all equality-case checks')


if __name__=='__main__': main()
