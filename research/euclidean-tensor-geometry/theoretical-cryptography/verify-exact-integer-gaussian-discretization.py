#!/usr/bin/env python3
"""Checks for integer-center Gaussian discretization; Python 3 standard library."""
from fractions import Fraction as F
from math import exp, factorial, floor, pi


def arctan_bracket(x, n=12):
    a = sum((-1)**i*x**(2*i+1)/(2*i+1) for i in range(n))
    b = a+(-1)**n*x**(2*n+1)/(2*n+1)
    return min(a,b), max(a,b)


def exp_bracket(x, n=20):
    assert 0 < x < n+2
    a = sum(x**i/factorial(i) for i in range(n+1))
    return a, a+(x**(n+1)/factorial(n+1))/(1-x/(n+2))


def check_constants():
    a, b = arctan_bracket(F(1,5))
    c, d = arctan_bracket(F(1,239))
    lo, hi = 16*a-4*d, 16*b-4*c  # Machin's formula
    assert F(314,100) < lo < hi < F(22,7)
    assert exp_bracket(F(12,5))[0] > 11
    assert exp_bracket(F(77,100))[1] < F(24,11)
    assert F(4,5)*lo-F(2,3)*(F(12,5)+1) > hi/50
    assert F(2,3)*F(77,100) > F(29,200)*hi
    assert (1+F(1,10))/(F(5,2)-F(1,10)) == F(11,24)
    ntests = 0
    for m in range(2,31):
        a = tuple(F(-1,10)+F(j,5*(m-1)) for j in range(m))
        weights = []
        for j, x in enumerate(a):
            p = F(1)
            for k,y in enumerate(a):
                if k != j:
                    p *= (1-y)/(x-y)
            weights.append(p)
        assert sum(weights) == 1
        assert sum(map(abs, weights)) <= F(11)**(m-1)*(m-1)**(m-1)/factorial(m-1)
        ntests += 1
    print(f"PASS exact interpolation signs and {ntests} Lagrange weight bounds")


def parameters(L):
    eps = F(0) if L < 2 else (L-1)/4
    assert 0 <= eps < F(1,2)
    return eps


def pair(L,k):
    eps = parameters(L)
    sgn = 1 if k>0 else -1
    return F(k)+eps*sgn, F(k)+(eps-L)*sgn


def check_pair_identities():
    cases = (F(101,100),F(11,10),F(3,2),F(19,10),F(199,100),F(2),
             F(201,100),F(9,4),F(5,2),F(11,4),F(29,10),F(299,100))
    count = 0
    for L in cases:
        eps = parameters(L)
        Delta, v = 1/(L-1), 1/L  # in units t^2=1
        assert Delta/(1+Delta) == v
        assert v > 0
        for k in (*range(-20,0),*range(1,21)):
            a,b = pair(L,k)
            assert a-b == (L if k>0 else -L)
            assert (a-b)/L in (-1,1)  # paired phases on the mean grid
            assert a*a > b*b
            assert v*(a*a-b*b) == 2*abs(k)+2*eps-L
            assert tuple(-q for q in pair(L,k)) == pair(L,-k)
            if L >= 2:
                ell = L-2
                closest = (k-2) if k>0 else (k+2)
                assert abs(b-closest) == abs(eps-ell) < F(1,2)
                assert v*(a*a-b*b)-Delta*(eps*eps-(eps-ell)**2) >= (2*eps-ell)/(1+ell) > 0
            else:
                assert v*(a*a-b*b) >= 2-L > 0
            count += 1
    print(f"PASS {count} exact frequency-pair and damping identities")


def numerical_operator(L, t, margin=12):
    # Normalized matrix T/D on nonzero Fourier rows and columns. The proof
    # bounds the whole infinite operator; these solve only finite truncations.
    ids = tuple(k for k in range(-margin,margin+1) if k)
    eps = float(parameters(L))
    delta, v = t*t/float(L-1), t*t/float(L)
    A = []
    for j in ids:
        row = []
        for k in ids:
            a,b = map(float,pair(L,k))
            row.append(exp(-pi*delta*((j-a)**2-eps**2))
                       - exp(-pi*(v*(a*a-b*b)+delta*((j-b)**2-eps**2))))
        A.append(row)
    R = [[x-int(i==j) for j,x in enumerate(row)] for i,row in enumerate(A)]
    norm = max(sum(abs(row[j]) for row in R) for j in range(len(ids)))
    assert norm < 1/2
    # Scale by the leading nonzero h/D coefficient so the residual is a
    # relative rather than a vacuous underflow-sized calculation.
    h = [exp(-pi*delta*(j*j-1)) for j in ids]
    x = [0.0]*len(ids)
    for _ in range(80):
        x = [-hj-sum(a*b for a,b in zip(row,x)) for hj,row in zip(h,R)]
    err = max(abs(hj+sum(a*b for a,b in zip(row,x))) for hj,row in zip(h,A))
    assert err < 1e-12
    assert all(abs(xj-xk)<1e-12 for xj,xk in zip(x,reversed(x)))
    total_coeff = exp(-pi*delta*(1-eps*eps))*sum(map(abs,x))
    assert 2*total_coeff < 1
    print(f"PASS finite truncation L={L}, t={t}, norm={norm:.6g}, scaled residual={err:.3g}")


if __name__ == "__main__":
    check_constants()
    check_pair_identities()
    for L,t in ((F(3,2),1),(F(19,10),2),(F(199,100),8),(F(2),2),
                (F(9,4),3),(F(5,2),3),(F(29,10),6),(F(299,100),20)):
        numerical_operator(L,t)
