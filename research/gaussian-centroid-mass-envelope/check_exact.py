#!/usr/bin/env python3
"""Pure rational replay of the *finite* algebra in the mass-envelope proof.

Purpose:
  - Verify prescribed masses of the threshold staircase symbolically.
  - Check the ordered residual-mass entropy inequality using exact
    rational interval enclosures for logarithms (no float operations).
  - Check weighted covariance and telescoping identities.
  - Test an intentionally unsorted negative control.

This checker does NOT attempt to prove the universal statements by
finite enumeration. Gaussian tail calculus and truncated-normal
variance inequalities are proved analytically in paper.md.

Python 3 standard library only.
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
import argparse
import hashlib
import json


SCALE=10**90


def ceil_div(a: int, b: int):
    assert b>0
    return -((-a)//b)


@lru_cache(maxsize=1)
def log_two_bounds():
    return atanh_series_bounds(F(1,3))


def atanh_series_bounds(z: F, terms: int=85):
    """Outward-rounded integer interval for log((1+z)/(1-z)).

    Each interval product is rounded outward to denominator 10^90.
    The nonnegative tail is bounded using a geometric majorant.
    This has rigorous inclusion despite large input denominators.
    """
    assert F(0)<=z<=F(1,3)
    zl=z.numerator*SCALE//z.denominator
    zu=ceil_div(z.numerator*SCALE,z.denominator)
    assert 0<=zl<=zu and zu*zu<SCALE*SCALE
    powerlo=zl
    powerhi=zu
    lower=upper=0
    for j in range(terms):
        denom=2*j+1
        lower+=2*powerlo//denom
        upper+=ceil_div(2*powerhi,denom)
        powerlo=powerlo*zl*zl//(SCALE*SCALE)
        powerhi=ceil_div(powerhi*zu*zu,SCALE*SCALE)
    # The upper power contains z^(2N+1) with outward rounding.
    tail=ceil_div(2*powerhi*SCALE*SCALE,
                  (2*terms+1)*(SCALE*SCALE-zu*zu))
    upper+=tail
    return F(lower,SCALE),F(upper,SCALE)


@lru_cache(maxsize=30000)
def log_bounds(x: F):
    """Exact rational interval containing log(x), x>0.

    Reduce x = 2**e * m, 1 <= m < 2; then
    log(m)=2atanh((m-1)/(m+1)) with 0<=z<1/3.
    Every arithmetic operation is on arbitrary-precision integers.
    """
    assert x>0
    if x==1:
        return F(0),F(0)
    e=x.numerator.bit_length()-x.denominator.bit_length()
    m=x/F(2)**e
    while m<1:
        e-=1
        m*=2
    while m>=2:
        e+=1
        m/=2
    assert F(1)<=m<F(2)
    z=(m-1)/(m+1)
    mlo,mhi=atanh_series_bounds(z)
    blo,bhi=log_two_bounds()
    if e>=0:
        lo=e*blo+mlo
        hi=e*bhi+mhi
    else:
        lo=e*bhi+mlo
        hi=e*blo+mhi
    assert lo<=hi
    return lo,hi


def residual_statistics(masses: tuple[F,...]):
    """Rational algebra and interval entropies for a mass vector."""
    assert len(masses)>=2 and all(x>0 for x in masses)
    assert sum(masses,F(0))==F(1)
    ps=sorted(masses,reverse=True)
    assert all(ps[i]>=ps[i+1] for i in range(len(ps)-1))
    Ss=[]
    rem=F(1)
    survival=F(1)
    for i,p in enumerate(ps):
        assert rem==sum(ps[i:],F(0))
        Ss.append(rem)
        if i<len(ps)-1:
            q=p/rem
            assert F(0)<q<F(1)
            # These products prove exact cell masses without evaluating
            # normal quantiles at all.
            assert survival==rem
            assert survival*q==p
            survival*=1-q
            rem-=p
        else:
            assert rem==p==survival
    Q=sum((p*p for p in ps),F(0))
    entropy_lower=F(0)
    entropy_upper=F(0)
    ordinary_entropy_upper=F(0)
    max_interval_width=F(0)
    for p,S in zip(ps,Ss):
        lo,hi=log_bounds(1/S)
        assert lo>=0
        entropy_lower+=p*p*lo
        entropy_upper+=p*p*hi
        ordinary_entropy_upper+=p*hi
        max_interval_width=max(max_interval_width,hi-lo)
    assert ordinary_entropy_upper<=1,("integral inequality",ps)
    assert entropy_upper<=Q,("negative covariance",ps)
    assert max_interval_width<F(1,10**65)
    # Strict known rough bound for the final missing cell:
    # phi(t_p)^2 <= p_min <= Q.
    assert ps[-1]<=Q
    return {
        "number_of_cells":len(ps),
        "S2":[Q.numerator,Q.denominator],
        "weighted_entropy_upper_lt_S2":entropy_upper<Q,
        "ordinary_entropy_upper_le_one":ordinary_entropy_upper<=1,
        "maximum_log_interval_width_lt_1e65":True,
        "last_mass_le_collision_mass":ps[-1]<=Q,
        "exact_partition_masses":True,
    }


def negative_control():
    """The sorted-order hypothesis is genuinely required."""
    unsorted=tuple([F(1,100)]*70+[F(3,10)])
    assert sum(unsorted,F(0))==1
    remaining=F(1)
    lo=F(0)
    hi=F(0)
    for p in unsorted:
        a,b=log_bounds(1/remaining)
        lo+=p*p*a
        hi+=p*p*b
        remaining-=p
    collision=sum((p*p for p in unsorted),F(0))
    assert lo>collision,("negative control failed",lo,collision)
    return True


def cases(quick: bool):
    yield "two_equal", [1,1]
    yield "three_equal", [1,1,1]
    yield "four_equal", [1,1,1,1]
    yield "two_extreme", [10**22,1]
    yield "multi_spike", [1000]+[1]*36
    yield "two_levels", [100]*13+[1]*97
    yield "rational_unequal", [F(1,2), F(1,3), F(1,9), F(1,18)]
    yield "powers_thirty_two", [2**i for i in range(32)]
    yield "stretched_masses", [(i*i+1) for i in range(45)]
    if not quick:
        yield "uniform_101", [1]*101
        yield "uniform_256", [1]*256
        yield "powers_sixty_four", [2**i for i in range(64)]
        yield "power_law_120", [F(1,i*i) for i in range(1,121)]
        yield "rational_pseudorandom_193", [1+(71*i*i+11*i+13)%997 for i in range(193)]
        yield "two_levels_640", [400]*40+[1]*600


def sharpened_scalar_constants_check():
    """Independent exact integer/rational bounds used in the -4,+3 proof."""
    assert F(8,3)**4 > F(16)*F(22,7)
    assert F(27,10)**7 > F(1000)
    assert log_bounds(F(2))[0]>F(2,3)
    assert log_bounds(F(10))[1]<F(7,3)
    assert log_bounds(F(16)*F(22,7))[1]<F(4)
    lower_ln10,upper_ln10=log_bounds(F(10))
    assert lower_ln10>2
    assert log_bounds(lower_ln10)[0]>F(2,3)
    # These are pure algebraic endpoints of the quantitative
    # Mills / mgf argument proved in paper.md; they are NOT
    # a grid verification of the universal Gaussian lemma.
    return True


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--quick",action="store_true")
    parser.add_argument("--json",action="store_true")
    args=parser.parse_args()
    report={"version":"1.0","arithmetic":"fractions.Fraction",
            "test_cases":[], "negative_control":False}
    for name,weights in cases(args.quick):
        weights=tuple(F(x) for x in weights)
        total=sum(weights,F(0))
        masses=tuple(x/total for x in weights)
        result=residual_statistics(masses)
        result["name"]=name
        report["test_cases"].append(result)
        if not args.json:
            print(f"PASS {name}: {result['number_of_cells']} exact masses, "
                  "outward-rational log intervals, sorted entropy bound")
    report["negative_control"]=negative_control()
    report["sharpened_scalar_constants"]=sharpened_scalar_constants_check()
    if not args.json:
        print("PASS exact rational constants for sharpened scalar "
              "Gaussian hazard bracket [-4,+3]")
        print("PASS negative control: reversing mass order can violate the "
              "sorted residual-mass entropy inequality")
        print(f"ALL CHECKS PASSED: {len(report['test_cases'])} positive cases, "
              "one certified negative case; zero floating point")
    else:
        print(json.dumps(report,sort_keys=True,indent=2))


if __name__=="__main__":
    main()
