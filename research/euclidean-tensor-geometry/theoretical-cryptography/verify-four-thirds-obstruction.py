#!/usr/bin/env python3
"""Exact finite exponent checks for exact-gaussian-four-thirds-obstruction.md."""

from fractions import Fraction as Q
from itertools import product


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def vec(x, y, k=1):
    return tuple(a+k*b for a, b in zip(x, y))


def lsq(x):
    return dot(x, x)


def gaussian_exponents():
    n = 0
    for d in (1, 2, 3):
        vals = (Q(-2), Q(-1, 3), Q(1, 4), Q(3, 2))
        records = tuple(product(vals, repeat=d))
        for t2, D in product((Q(1, 2), Q(1), Q(4)), (Q(1, 3), Q(3, 2), Q(7))):
            s2 = t2 + D
            A = s2 / D
            omega = (1 - 1/A)*D
            assert t2*D == s2*omega
            assert D*(A-4) == 4*t2-3*s2
            for x, u in product(records, repeat=2):
                assert lsq(vec(u,x,-1))/t2 + lsq(x)/D == (
                    lsq(u)/s2 + lsq(vec(x,u,-1/A))/omega
                )
                n += 1
    return n


def linear_combo(basis, coeff):
    return tuple(sum(k*b[j] for b,k in zip(basis,coeff)) for j in range(len(basis)))


def aliasing():
    bases = (
        ((1,),),
        ((1,0),(0,2)),
        ((1,0),(Q(1,3),Q(3,2))),
        ((1,0,0),(Q(1,4),Q(3,2),0),(Q(-1,4),Q(1,3),2)),
    )
    vals = tuple(map(Q, ("-3","-1","0","1","3")))
    n = main = gaps = 0
    for basis in bases:
        d = len(basis)
        v = basis[0]
        lam2 = lsq(v)
        # Choose first shell direction v. For these triangular examples its
        # shortestness follows from the last nonzero coordinate in the basis.
        W = [linear_combo(basis, coeff) for coeff in product(range(-2,3), repeat=d)
             if any(coeff)]
        for A in map(Q, ("4","17/4","5","6")):
            p = tuple(A*x/2 for x in v)
            B2 = (A/2-1)**2*lam2
            assert B2-lam2 == lam2*A*(A-4)/4
            for w in W:
                r2 = lsq(w)
                c0 = dot(v,w)/r2
                assert r2 >= lam2 and abs(c0) <= 1
                minimum = r2*(A/2+c0)**2
                assert (A-2)-2*c0 >= 0
                assert minimum >= B2
                assert (minimum == B2) == (w == tuple(-x for x in v))
                gaps += 1
                for z in product(vals, repeat=d):
                    q = dot(z,w)/r2
                    if q < -A/2:
                        continue
                    F = lsq(vec(z,v,-1)) + (A-1)*(2*dot(z,w) + A*r2)
                    assert F >= r2*((q-c0)**2 + (A-1)*(2*q+A)) >= minimum
                    n += 1
                if w == tuple(-x for x in v):
                    assert lsq(vec(p,v,-1))+(A-1)*(2*dot(p,w)+A*r2) == B2
                    for x in vals:
                        if x > A/2:
                            continue
                        z = tuple(x*y for y in v)
                        F = lsq(vec(z,v,-1)) + (A-1)*(2*dot(z,w)+A*r2)
                        assert F >= B2+A*lam2*(A/2-x)
                        main += 1
    return n, gaps, main


if __name__ == "__main__":
    c = gaussian_exponents()
    a, b, d = aliasing()
    print(f"PASS: {c} exact completed-square exponent comparisons")
    print(f"PASS: {a} half-space inequalities, {b} unique-alias gaps, {d} normal slopes")
