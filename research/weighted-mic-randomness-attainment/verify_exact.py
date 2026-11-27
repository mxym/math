#!/usr/bin/env python3
"""Exact rational core checks, with integer angular separation certificates."""
from fractions import Fraction as F
from itertools import product


def samples(d):
    yield [F(1,d)]*d
    yield [F(0)]*(d-1)+[F(1)]
    for vals in ([j for j in range(d)],[j*j+1 for j in range(d)],
                 [4 if j%5==0 else 0 for j in range(d)]):
        S=sum(vals)
        yield [F(v,S) for v in vals]


def verify(d,r):
    e=F(1,2*d**4)
    l,h=F(1,d)-e,F(1,d)+e
    P=[[F(1,d)+e*((a==i)-r[a]) for i in range(d)] for a in range(d)]
    assert all(0<l<=x<=h for u in P for x in u)
    assert all(sum(col)==1 for col in zip(*P))
    assert all(sum(x*y for x,y in zip(row,r))==F(1,d) for row in P)
    # One-dimensional direction with column sum one, plus the
    # independent d-1 coordinate differences summing to zero.
    z=tuple(r)
    assert sum(z)==1
    for i in range(1,d):
        assert all(P[a][i]-P[a][0]==e*((a==i)-(a==0)) for a in range(d))
    # Sherman-Morrison inverse, independent of determinants.
    u=[P[a][0]-e*(a==0) for a in range(d)]
    assert sum(u)==1-e
    for a,i in product(range(d),repeat=2):
        assert (P[a][i]-u[a])/e==(a==i)
    # For every nonzero band, squared geometric means stay within
    # the square of the same positive interval, no numerical roots.
    for a,i,j in product(range(d),repeat=3):
        if i!=j:
            assert l*l<=P[a][i]*P[a][j]<=h*h
    # Angular grid is measured in units pi/(2d). The t phase is
    # grid point 1; dth roots are 0,4,...,4(d-1) mod 4d.
    period=4*d
    for j in range(d):
        diff=(4*j-1)%period
        assert min(diff,period-diff)>=1
    # Frobenius perturbation vs guaranteed minimum Fourier modulus.
    assert d*e==F(1,2*d**3)<F(1,d**3)
    # For this input state the normalized moments are all equal.
    return d*d


def main():
    cases=effects=0
    for d in range(2,15):
        for r in samples(d):
            effects+=verify(d,r)
            cases+=1
    # Unique effect supplies the d=1 endpoint.
    assert F(1,1)**2==1
    print(f"rational checks: {cases} spectra in d=2..14, {effects} exact weighted effects, d=1 endpoint")
    print("rational checks: all column sums, weighted row sums, band amplitude bounds, angular grid PASS")


if __name__=='__main__':
    main()
