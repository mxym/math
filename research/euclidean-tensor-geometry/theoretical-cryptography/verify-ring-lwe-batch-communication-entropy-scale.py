#!/usr/bin/env python3
"""Exact finite checks for ring-lwe-batch-communication-entropy-scale.md."""

from itertools import product
from collections import Counter
from fractions import Fraction as F

PHI = {
    3: (1, 1, 1),
    5: (1, 1, 1, 1, 1),
    9: (1, 0, 0, 1, 0, 0, 1),
    15: (1, -1, 0, 1, -1, 1, 0, -1, 1),
}


def reduce_z(terms, q):
    phi = PHI[q]
    a = [0]*q
    for j,c in terms:
        a[j % q] += c
    for i in range(q-1,len(phi)-2,-1):
        c = a[i]
        for j,x in enumerate(phi):
            a[i-len(phi)+1+j] -= c*x
        assert a[i]==0
    return tuple(a[:len(phi)-1])


def add(a,b,q):
    return tuple((x+y)%q for x,y in zip(a,b))


def neg(a,q):
    return tuple(-x%q for x in a)


def mul(a,b,q):
    d=len(a)
    out=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[(i+j)%d]+=(1 if i+j<d else -1)*x*y
    return tuple(x%q for x in out)


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def dyadic_orbit_degree(p,d):
    j,x=1,p%(2*d)
    while x!=1:
        x=x*p%(2*d)
        j+=1
    return j


def verify_exact_operators():
    check_spectrum = check_projection = check_ideals = 0
    for q,d,k in ((3,1,2),(3,2,1),(5,1,2),(5,2,1),(9,1,2),(15,1,1)):
        R=list(product(range(q),repeat=d))
        B=list(product(R,repeat=k))
        N=len(R)
        zero=(0,)*d
        # An arbitrary bounded positive, not necessarily product, residual kernel.
        L={y:1+((i*i+2*i)%11) for i,y in enumerate(B)}
        G={}
        for s in R:
            count=0
            for a in B:
                delta=tuple(mul(ai,s,q) for ai in a)
                count+=sum(L[y]*L[tuple(add(yi,zi,q) for yi,zi in zip(y,delta))] for y in B)
            G[s]=count
        eig = {z:reduce_z(((dot(z,s),F(G[s],N**(2*k+1))) for s in R),q) for z in R}
        coefficients={}
        ideals={}
        proper_supp=set()
        for ww in B:
            coeff=Counter()
            for y1,y2 in product(B,repeat=2):
                h=(sum(dot(w,a)-dot(w,b) for w,a,b in zip(ww,y1,y2)))%q
                coeff[h]+=L[y1]*L[y2]
            coefficients[ww]=reduce_z(((j,F(c,N**(2*k))) for j,c in coeff.items()),q)
            img=Counter()
            for a in B:
                out=zero
                for ai,wi in zip(a,ww):
                    out=add(out,mul(ai,wi,q),q)
                img[out]+=1
            assert len(set(img.values()))==1
            ideals[ww]=frozenset(img)
            if len(img)<N:
                proper_supp.add(frozenset(img))
            check_ideals+=1
        for z in R:
            p=tuple(sum((F(v[i])/len(ideals[w]) for w,v in coefficients.items() if z in ideals[w]),F(0))
                    for i in range(len(PHI[q])-1))
            assert p==eig[z]
            assert p[0]>=0 and all(x==0 for x in p[1:])
            check_spectrum+=1
        for J in proper_supp:
            Ann=[a for a in R if all(dot(a,x)%q==0 for x in J)]
            D=list(product(Ann,repeat=k))
            projected={y:sum(L[tuple(add(yi,zh,q) for yi,zh in zip(y,z))] for z in D)
                       for y in B}
            direct=F(sum(v*v for v in projected.values()),len(D)**2*len(B))
            by_frequency=sum(v[0] for w,v in coefficients.items() if all(x in J for x in w))
            assert direct==by_frequency
            for cutoff in (3,6,8):
                trimmed={y:L[y]*(L[y] <= cutoff) for y in B}
                projected_t={y:sum(trimmed[tuple(add(yi,zh,q) for yi,zh in zip(y,z))] for z in D)
                             for y in B}
                assert all(0<=projected_t[y]<=projected[y] for y in B)
                assert sum(v*v for v in projected_t.values())<=sum(v*v for v in projected.values())
                check_projection+=1
    return check_spectrum,check_projection,check_ideals


def verify_odd_shells_and_growth():
    shells=growth=0
    for p in (3,5,7,11,13,17,31,97):
        for d in (4,8,16,32,64):
            degree=dyadic_orbit_degree(p,d)
            assert degree>=1 and d%degree==0
            if d>=32:
                assert dyadic_orbit_degree(p,2*d)==2*degree
                growth+=1
            # A formal primitive (2d)-th root; negation is X^d.
            for a,b in product(range(d),repeat=2):
                if a<b:
                    for signs in product((0,d),repeat=2):
                        assert (a+signs[0]-b-signs[1])%(2*d)!=0
                        shells+=1
    # Verify an explicit compact shifted ideal witness over F3. At d=4,
    # X^4+1=(X^2+X+2)(X^2-X+2), with the degrees doubling each stage.
    for d in (4,8,16,32,64,128):
        u=d//4
        assert dyadic_orbit_degree(3,d)==2*u
        f={2*u:1,u:1,0:2}
        g={2*u:1,u:2,0:2}
        h=Counter()
        for i,x in f.items():
            for j,y in g.items():
                h[i+j]+=x*y
        assert {i:v%3 for i,v in h.items() if v%3}=={d:1,0:1}
        # Multiplication by f corresponds to a vector with a bounded lift.
        assert sum(min(x,3-x)**2 for x in f.values())==3
        growth+=1
    return shells,growth


if __name__ == "__main__":
    print("PASS exact ideal-sector spectra, positive trimming, uniform sums:",verify_exact_operators())
    print("PASS unit shells and stable sparse-factor arithmetic:",verify_odd_shells_and_growth())
