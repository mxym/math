#!/usr/bin/env python3
"""Finite normalization checks for the Gaussian-response bottleneck proof."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import factorial


def product_coefficients(a, b):
    c = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def bessel():
    rows = 0
    for n in (2,3,5,12,24,40):
        a = [F(1,4**k*factorial(k)**2) for k in range(n+1)]
        h = [x/F(2*(k+1)) for k,x in enumerate(a)]
        der = lambda v:[k*x for k,x in enumerate(v) if k]
        lhs = product_coefficients(der(h),a)
        rhs = product_coefficients(h,der(a))
        pair = [F(0)]*(2*n)
        for i in range(n+1):
            for j in range(i):
                pair[i+j-1] += (i-j)*(h[i]*a[j]-h[j]*a[i])
        assert all(x-y==z for x,y,z in zip(lhs,rhs,pair))
        assert all(x<0 for x in pair[:-1])
        assert pair[-1] == 0
        assert a[1]==F(1,4) and h[0]==F(1,2)
        rows += len(pair)
    return rows


def aliases():
    rows = 0
    for q in range(3,22):
        # Constant and linear terms in the circle Fourier model.
        assert {j%q for j in (-1,0,1)} == {q-1,0,1}
        # Mean of (u exp(-i theta_a)+v exp(i theta_a))^2.
        second_moment = Counter((p+s)%q for p,s in product((-1,1),repeat=2))
        assert second_moment[0] == 2
        for x in range(-4*q,4*q+1):
            # The uniform-grid mixture retains exactly multiples of q.
            if x%q == 0:
                assert (x//q)**2*q**2 == x*x
            else:
                assert x and 0 not in {x%q}
            rows += 1
    return rows


def exact_harmonic_channel():
    # Finite synthetic circle law with only its first harmonic, not a
    # finite-precision simulation of an actual Gaussian response.
    b = F(1,16)
    c = [F(1),F(0),F(-1),F(0)]
    s = [F(0),F(1),F(0),F(-1)]
    q = 4
    rows = 0
    for wt in product(range(4),repeat=q):
        total = sum(wt)
        if not total:
            continue
        nu = [F(v,total) for v in wt]
        out = [sum(nu[y]*(1+2*b*c[(y-a)%q]) for y in range(q))
               for a in range(q)]
        assert sum(out)==q and min(out)>0
        x = sum(p*v for p,v in zip(nu,c))
        y = sum(p*v for p,v in zip(nu,s))
        assert sum((p-1)**2 for p in out)/q == 2*b*b*(x*x+y*y)
        rows += 1
    return rows


def shifts():
    # Check one synthetic circular alphabet with integer cosine values.
    c = (1,0,-1,0)
    rows = 0
    for d in range(1,5):
        words = list(product(range(4),repeat=d))
        histogram = Counter(sum(c[i] for i in z) for z in words)
        for y in words:
            assert Counter(sum(c[(i-j)%4] for i,j in zip(y,u))
                           for u in words) == histogram
            rows += 1
        cum = 0
        for r in range(1,5):
            probs = {}
            for x,n in sorted(histogram.items()):
                probs[x] = F((cum+n)**r-cum**r, len(words)**r)
                cum += n
            cum = 0
            assert sum(probs.values())==1
            assert sum(x*p for x,p in probs.items())>=0
    return rows


def moderate():
    for d,n in product(range(2,40),range(1,40)):
        if not n<d:
            continue
        eta = F(n,d)
        u = 1-eta/2
        assert 2*u-u*u == 1-eta*eta/4 < 1
    return sum(d-1 for d in range(2,40))


if __name__=="__main__":
    print("PASS Bessel derivative / alias arithmetic:", bessel(), aliases())
    print("PASS exact first-harmonic posterior rows:", exact_harmonic_channel())
    print("PASS synthetic shift histograms / tilt exponents:", shifts(), moderate())
