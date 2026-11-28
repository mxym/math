#!/usr/bin/env python3
"""Identity checks for the standalone smoothed Gaussian projection proof."""
from fractions import Fraction as F
from itertools import product
from math import ceil, cos, exp, fsum, hypot, log, pi, sin, sqrt


def square_identities():
    count = 0
    for d in (2, 3, 4):
        for r in range(1, d):
            for s, h in product((F(1, 2), F(3, 2), F(5)), (F(1, 13), F(2, 3), F(3))):
                e = 1 + h*h
                for x in product((-2, 1, 3), repeat=d):
                    for y in product((F(0), F(3, 7)), repeat=r):
                        raw = sum(t*t for t in x)/(s*s) + sum(
                            (z-F(t)/s)**2 for t, z in zip(x, y))/(h*h)
                        split = (sum(z*z for z in y)/e
                                 + sum(t*t for t in x[r:])/(s*s)
                                 + e/(s*s*h*h)*sum(
                                     (t-s*z/e)**2 for t, z in zip(x,y)))
                        assert raw == split
                        adual = s*s*(sum(t*t for t in x[r:])
                                     + h*h/e*sum(t*t for t in x[:r]))
                        phase_damp = s*s/e*sum(t*t for t in x[:r])
                        assert adual + phase_damp == s*s*sum(t*t for t in x)
                        count += 1
    return count


def dot(u, v):
    return u[0]*v[0] + u[1]*v[1]


def norm2(v):
    return dot(v,v)


def frequency_rows(s, h, u):
    """Only two-dimensional mathematical checking, via a unimodular basis."""
    w = (-u[1], u[0])
    beta = s*h/sqrt(1+h*h)
    def image(k):
        return (beta*dot(u,k), s*dot(w,k))

    a, b = (1,0), (0,1)
    for _ in range(100):
        va, vb = image(a), image(b)
        if norm2(vb) < norm2(va):
            a, b = b, a
            continue
        m = round(dot(va,vb)/norm2(va))
        if m == 0:
            break
        b = b[0]-m*a[0], b[1]-m*a[1]
    else:
        raise AssertionError("finite toy basis loop")
    va, vb = image(a), image(b)
    det = abs(va[0]*vb[1]-va[1]*vb[0])
    assert abs(a[0]*b[1]-a[1]*b[0]) == 1
    R = 4.2
    I, J = ceil(R*hypot(*vb)/det), ceil(R*hypot(*va)/det)
    rows = []
    for i, j in product(range(-I,I+1), range(-J,J+1)):
        v = (i*va[0]+j*vb[0], i*va[1]+j*vb[1])
        if norm2(v) <= R*R:
            k = (i*a[0]+j*b[0], i*a[1]+j*b[1])
            coef = exp(-pi*norm2(v))
            slope = s*dot(u,k)/(1+h*h)
            full = exp(-pi*s*s*norm2(k))
            assert abs(coef*exp(-pi*(1+h*h)*slope*slope)-full) < 5e-14
            rows.append((i,j,coef,slope))
    assert (0,0,1.0,0.0) in rows
    return rows


def direct_checks():
    count, integrals = 0, []
    for s, h, v in ((2.5, .30, (1,0)), (4.0,.093,(1,sqrt(2))),
                    (5.0,.061,(2,1)), (8.0,.02,(1,(sqrt(5)-1)/2))):
        length = hypot(*v)
        u = tuple(a/length for a in v)
        rows = frequency_rows(s,h,u)
        factors = [(c,2*pi*b) for i,j,c,b in rows if (i,j) != (0,0)]
        D = fsum([1.0]+[c*exp(-pi*(1+h*h)*b*b)
                         for i,j,c,b in rows if (i,j) != (0,0)])
        X = [(dot(u,k)/s, exp(-pi*norm2(k)/(s*s)))
             for k in product(range(-ceil(6*s),ceil(6*s)+1), repeat=2)]
        mass = fsum(a for _,a in X)
        scale = sqrt(1+h*h)
        for y in (-.8, -.311, 0.0, .137, .66):
            q = exp(-pi*(y/scale)**2)/scale
            direct = fsum(a*exp(-pi*((y-z)/h)**2)
                          for z,a in X)/(h*mass*q)
            via_fourier = (1+fsum(a*cos(b*y) for a,b in factors))/D
            assert abs(direct-via_fourier) < 3e-11
            count += 1

        N = 12000
        dx = 8/N
        tv = dx/2*fsum(
            abs((1+fsum(a*cos(b*y) for a,b in factors))/D-1)
            *exp(-pi*(y/scale)**2)/scale
            for y in (-4+(j+.5)*dx for j in range(N)))
        N2 = 107
        torus = fsum(abs(fsum(c*cos(2*pi*(i*u+j*v)/N2)
                             for i,j,c,_ in rows if (i,j) != (0,0)))
                     for u,v in product(range(N2),repeat=2))/(2*N2*N2)
        assert abs(tv-torus) < .009
        integrals.append((round(tv,7),round(torus,7)))
    return count, integrals


def periodic_checks():
    lam = (3+sqrt(5))/2
    xi = lam-2
    u = (1/hypot(1,xi),xi/hypot(1,xi))
    w = (-u[1],u[0])
    T = log(lam)
    for x in product(range(-4,5),repeat=2):
        Mx = (2*x[0]+x[1],x[0]+x[1])
        assert abs(exp(-T)*dot(u,Mx)-dot(u,x)) < 2e-14
        assert abs(exp(T)*dot(w,Mx)-dot(w,x)) < 2e-14
    t, c = .18, 20
    b = exp(-2*t)*u[0]**2+exp(2*t)*w[0]**2
    assert b < .91
    a = exp(-pi*c)
    square_upper = 2*a/(1-a)**2
    other_lower = .5*exp(-pi*c*b)
    assert other_lower > square_upper
    return 81, round(b,9)


def main():
    print("PASS exact square/Poisson exponents:",square_identities())
    print("PASS densities and illustrative (real TV, torus TV):",direct_checks())
    print("PASS periodic lattice rows and decreasing length:",periodic_checks())


if __name__ == "__main__":
    main()
