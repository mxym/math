#!/usr/bin/env python3
"""Exact finite checks for dyadic-log-sparse-spectral-peaks.md."""

from fractions import Fraction
from itertools import combinations, product
from math import factorial, gcd, prod


def relations(a,H,M):
    return [m for m in product(range(-H,H+1),repeat=len(a))
            if any(m) and sum(x*y for x,y in zip(m,a))%M==0]


def angular_arithmetic():
    generic=bad=joins=none=0
    for M,H,k in ((64,2,3),(128,2,3),(128,3,2),(256,6,2)):
        reps=tuple(range(1,M//2,2))
        for A in combinations(reps,k):
            rr=relations(A,H,M)
            if not rr:
                # Exact average of a finite product of Fourier polynomials.
                total=0
                for m in product(range(-H,H+1),repeat=k):
                    if sum(x*y for x,y in zip(m,A))%M==0:
                        total+=prod(3+j+v for j,v in enumerate(m))
                assert total==prod(range(3,3+k))
                generic+=1
            else:
                base=()
                for a in A:
                    if not relations(base+(a,),H,M):
                        base+=(a,)
                assert 1<=len(base)<len(A)
                for b in A:
                    if b in base:
                        continue
                    out=relations(base+(b,),H,M)
                    assert out and all(m[-1]!=0 for m in out)
                    assert all(gcd(abs(m[-1]),M)<=H for m in out)
                bad+=1
        for s in (1,2):
            bases = tuple(combinations(reps[::max(1,len(reps)//8)],s))
            for B in bases:
                if relations(B,H,M):
                    continue
                V = tuple(product(range(-(H//3),H//3+1),repeat=s))
                for b in reps:
                    if b in B:
                        continue
                    opts=[v for v in V if (sum(x*y for x,y in zip(v,B))+b)%M==0]
                    assert len(opts)<=1
                    if opts:
                        v=opts[0]
                        assert sum(v)%2==1 and sum(abs(x) for x in v)>=3
                        joins+=1
                    else:
                        none+=1
    return generic,bad,joins,none


def bessel_coeff(m,power):
    d=power-m
    if d<0 or d%2:
        return Fraction(0)
    j=d//2
    return Fraction(1,2**power*factorial(j)*factorial(j+m))


def harmonic_recurrence():
    z=0
    for m,p in product(range(1,15),range(31)):
        assert bessel_coeff(m-1,p-1)-bessel_coeff(m+1,p-1)==2*m*bessel_coeff(m,p)
        # Formal series coefficient version of I_m <= I_0*(t/2)^m/m!.
        d=p-m
        if d>=0:
            assert bessel_coeff(m,p)<=bessel_coeff(0,d)*Fraction(1,2**m*factorial(m))
        z+=1
    return z


if __name__=="__main__":
    a,b,c,d=angular_arithmetic()
    e=harmonic_recurrence()
    print(f"PASS: {a} generic Fourier averages, {b} maximal bad bases")
    print(f"PASS: {c} truncated harmonic joins, {d} absent joins, {e} Bessel coefficient identities")
