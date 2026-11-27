#!/usr/bin/env python3
"""Independent enumeration of small field subspaces and bin incidences."""
from fractions import Fraction as F
from itertools import product
from math import isqrt


def mul(a,b,q):
    if q != 4:
        return a*b % q
    # F4 = F2[omega]/(omega^2+omega+1); bit encoding.
    r = (a if b&1 else 0) ^ ((a << 1) if b&2 else 0)
    return r ^ (7 if r&4 else 0)


def add(a,b,q):
    if q == 4:
        return tuple(x^y for x,y in zip(a,b))
    return tuple((x+y)%q for x,y in zip(a,b))


def scalar(c,x,q):
    return tuple(mul(c,a,q) for a in x)


def spaces(q,N,r,V):
    if r == N:
        return [frozenset(V)]
    z = (0,)*N
    D = {frozenset([z])}
    for _ in range(r):
        D = {frozenset(add(a,scalar(c,x,q),q) for c in range(q) for a in W)
             for W in D for x in V if x not in W}
    return sorted(D,key=lambda X:tuple(sorted(X)))


def fibers(q,V,W):
    R = set(V)
    while R:
        a = min(R)
        B = {add(a,w,q) for w in W}
        R -= B
        yield B


def root(x):
    den = 1 << 34
    lo = F(isqrt(x.numerator*den**2//x.denominator),den)
    return lo,lo if lo**2==x else lo+F(1,den)


def cs(q,N,r,V,D):
    z = V[0]
    x = V[1]
    m = q**(N-r)
    pair = [W for W in D if x in W]
    p2 = F(len(pair),len(D))
    assert p2 == F(q**r-1,q**N-1)
    assert F(q-1,q*m) <= p2 <= F(1,m)
    line = {scalar(a,x,q) for a in range(q)}
    cases = 0
    for w in V:
        if w not in (z,x):
            hit = F(sum(w in W for W in pair),len(pair))
            if w in line:
                assert hit == 1
            else:
                assert hit == F(q**r-q,q**N-q) <= F(1,m)
            cases += 1
    # Check actual (translated) bins by conditioning on a pair of arbitrary words.
    v = V[-1]
    joint = sum(z in B and v in B for W in D for B in fibers(q,V,W))
    assert F(joint,len(D)*m) == p2/m
    return cases


def profiles(V):
    n = len(V)
    # Same-class pairs, cross-class singletons, mixed weights, dense tails
    # and an exact all-zero-error one-point control.
    for labels in ([1]*n, [0]*(n-2)+[2,3],
                   [1 if j % 5 else 3 for j in range(n)],
                   [(j*j+j+3)%7 for j in range(n)],
                   [0]*(n-1)+[1]):
        yield {x:w for x,w in zip(V,labels)}


def check(q,N,r,V,D,weights):
    m = q**(N-r)
    total = sum(weights.values())
    p = {x:F(w,total) for x,w in weights.items()}
    sizes = {u:sum(w==u for w in p.values()) for u in set(p.values()) if u>0}
    psi = {u:u*s*min(1,F(s,m)) for u,s in sizes.items()}
    same = max([u for w,u in psi.items() if sizes[w]>=2]+[F(0)])
    cross = max([u*v for x,u in psi.items() for y,v in psi.items() if x!=y]+[F(0)])
    c = F(q-1,2*q*(q+1))
    # Eq. (2) has the factor 1/sqrt(2) below this computed quantity.
    lo_min = c*max(same, root(cross)[0])
    hi_max = sum(root(x)[1] for x in psi.values())**2
    a = b = F(0)
    multi = len(sizes) > 1 or max(sizes.values()) > 1
    for W in D:
        for B in fibers(q,V,W):
            mass = sum(p[x] for x in B)
            S = mass*mass-sum(p[x]**2 for x in B)
            L,H = root(S)
            a += L
            b += H
    a /= len(D)
    b /= len(D)
    assert a >= lo_min and b <= hi_max + F(1,1<<25)
    assert (a>0) == multi
    return multi


def main():
    Ncase=Nspace=Nthird=Nprofile=Nz=0
    for q,Ns in ((2,range(1,5)),(3,range(1,4)),(4,range(1,4))):
        for N in Ns:
            V = list(product(range(q),repeat=N))
            for r in range(1,N+1):
                D = spaces(q,N,r,V)
                assert all(len(W)==q**r for W in D)
                ratio = F(1)
                for j in range(r):
                    ratio *= F(q**N-q**j,q**r-q**j)
                assert len(D) == ratio
                Nthird += cs(q,N,r,V,D)
                Ncase += 1
                Nspace += len(D)
                for P in profiles(V):
                    Nz += not check(q,N,r,V,D,P)
                    Nprofile += 1
    assert Nz == Ncase
    assert mul(2,2,4)==3 and mul(2,3,4)==1
    print(f"occupancy: {Ncase} rank/field cases q=2,3,4, {Nspace} subspaces, {Nthird} third-point conditions")
    print(f"occupancy: {Nprofile} exact-rational support/weight profiles, {Nz} single-support zero controls PASS")


if __name__ == '__main__':
    main()
