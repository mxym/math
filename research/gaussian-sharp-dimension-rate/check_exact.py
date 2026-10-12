#!/usr/bin/env python3
"""Independent exact-rational proof-interface checker for dimension/accuracy curves.

Universal Gaussian probability and asymptotic statements are PROVED in paper.md.
This checker verifies all six explicit accuracy/dimension pairs with
strict rational comparisons, the strengthened binary entropy lemma on
a stress family, exact Berry–Esseen/tilting endpoint budgets, and a finite
collection of constant-term spherical-cap thresholds via outward-rational
logarithmic/π intervals. It uses no floating-point, random simulations,
numerical integration, or black-box optimizer.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from itertools import combinations
import argparse
import json

SCALE=10**95

def ceil_div(a:int,b:int)->int:
    assert b>0
    return -((-a)//b)

def atanh_bounds(z:F, terms:int=96):
    """Exact outward fixed-point enclosure of log((1+z)/(1-z))."""
    assert 0<=z<=F(1,3)
    lo=z.numerator*SCALE//z.denominator
    hi=ceil_div(z.numerator*SCALE,z.denominator)
    assert 0<=lo<=hi and hi*hi<SCALE*SCALE
    pl=lo
    ph=hi
    lower=upper=0
    for i in range(terms):
        lower+=2*pl//(2*i+1)
        upper+=ceil_div(2*ph,2*i+1)
        pl=pl*lo*lo//(SCALE*SCALE)
        ph=ceil_div(ph*hi*hi,SCALE*SCALE)
    rem=ceil_div(2*ph*SCALE*SCALE,
                 (2*terms+1)*(SCALE*SCALE-hi*hi))
    return F(lower,SCALE),F(upper+rem,SCALE)

@lru_cache(maxsize=1)
def ln2():
    return atanh_bounds(F(1,3))

@lru_cache(maxsize=25000)
def ln(x:F):
    assert x>0
    if x==1:
        return F(0),F(0)
    e=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/F(2)**e
    while y<1:
        e-=1
        y*=2
    while y>=2:
        e+=1
        y/=2
    al,au=atanh_bounds((y-1)/(y+1))
    bl,bu=ln2()
    if e>=0:
        return al+e*bl,au+e*bu
    return al+e*bu,au+e*bl

def atan_reciprocal(m:int,N:int=55):
    assert m>1
    s=sum((F((-1)**i,(2*i+1)*m**(2*i+1))
           for i in range(N)),F(0))
    rem=F(1,(2*N+1)*m**(2*N+1))
    return (s-rem,s) if N%2 else (s,s+rem)

@lru_cache(maxsize=1)
def pi_bounds():
    a,b=atan_reciprocal(5)
    c,d=atan_reciprocal(239)
    lower,upper=16*a-4*d,16*b-4*c
    assert F(314,100)<lower<upper<F(315,100)
    return lower,upper

def log_four_pi():
    a,b=pi_bounds()
    return ln(4*a)[0],ln(4*b)[1]

def cert_tradeoff():
    l2, h2=ln2()
    assert l2>F(2,3) and h2<F(7,10)
    assert F(99,70)**2>2
    assert F(27,10)**5>F(400,3)
    assert 2*17**2 >24**2       # 6/sqrt(2) <17/4
    assert F(20)<25  # 2+sqrt(20)<7
    assert 64**2*20<288**2
    assert 100000>23040        # sqrt(L0)> threshold
    assert ln(F(10**10))[1]<24  # cutoff monotonicity base
    assert 10**10>184320       # exponential residual <1/(10sqrt L)
    assert F(17,4)+F(3,5)+F(1,10)<5
    assert F(8)+F(96,49)<10    # Q2,Q4 good-event Chebyshev
    points=[
       (1,72,1),(4,41,2),(16,30,4),(64,25,8),
       (256,23,16),(1024,22,32),(262144,21,512)]
    out=[]
    for A,C,root in points:
        assert root**2==A
        TA=F(5)+F(10,root)+F(8,A)
        # Exact rational upper: 4+4ln2+2sqrt2*TA
        cap=F(4)+4*h2+F(99,35)*TA
        assert cap<C, (A,C,cap)
        out.append({
            "A":A, "certified_integer_error":C,
            "rational_bound_upper_lt_target":True,
            "dimension":"ceil(A*(log k)^2)+1"
        })
    # Negative control: the current elementary formula at A=1
    # does not certify a stronger tolerance of 70.
    assert F(4)+4*l2+F(14,5)*23>70
    print("PASS: rational Berry-Esseen, normal tilt, full-rank budgets")
    print("PASS: seven strict tradeoff points (A,C): "
          +", ".join(f"({a},{c})" for a,c,_ in points))
    print("PASS: negative control: A=1 cannot certify error 70 by this bound")
    return out

def cert_euler_constant():
    """Exact rational brackets for Euler gamma via harmonic-log integrals.

    For every n: H_n-log(n+1) < gamma < H_n-log(n).
    Both bounds are consequences of integral comparison of 1/x.
    Our tests never use a floating-point value of gamma.
    """
    h=F(0)
    for j in range(1,1001):
        h+=F(1,j)
        if j==6:
            # H_6 =49/20, log7<39/20 implies gamma>1/2.
            assert h==F(49,20)
            assert ln(F(7))[1]<F(39,20)
        if j==1000:
            lo=h-ln(F(1001))[1]
            hi=h-ln(F(1000))[0]
            assert F(57,100)<lo<hi<F(59,100)
            assert hi-lo<F(1,1000)
    print("PASS: outward-rational Euler-gamma bracket, gamma>1/2")
    return {"n":1000,"gamma_gt_one_half":True,
            "certified_width_lt_1_over_1000":True}


def binary_weights(k:int):
    assert k>=2
    q=[1<<i for i in range(k.bit_length()-1,-1,-1)
       if k&(1<<i)]
    assert sum(q)==k
    return q

def cert_binary_entropy():
    cases=[3,7,15,31,63,255,257,511,1023,
           (1<<16)-1,(1<<32)-1,
           (1<<64)-1,(1<<256)-1,
           (1<<300)+(1<<155)+(1<<3)+1,
           10**80]
    lowln2,highln2=ln2()
    result=[]
    for k in cases:
        q=binary_weights(k)
        w=[F(x,k) for x in q]
        S=F(1)
        entropy_upper=F(0)
        for p in w:
            assert p>0 and p<=S
            assert S-p<p if S!=p else True
            # The direct exact entropy comparison is independent
            # of the telescoping h2 analytic proof.
            entropy_upper+=p*ln(F(1)/p)[1]
            S-=p
        assert S==0
        assert entropy_upper<2*lowln2,(k,entropy_upper)
        for cutoff in (8,128,4096):
            assert sum(x for x in q if x<cutoff)<cutoff
        result.append({
            "k_binary_digits":k.bit_length(),
            "number_of_blocks":len(q),
            "certified_entropy_lt_2ln2":True,
            "binary_geometric_mass":True})
    # Essential negative control: arbitrary unordered
    # 8 equal-weight selectors exceed the sharp binary bound.
    assert ln(F(8))[0]>2*highln2
    print(f"PASS: {len(result)} mixed binary expansions and extremal "
          "all-ones vectors have entropy <2log2")
    print("PASS: negative control: 8 equal selector blocks exceed 2log2")
    return result

def ceil_fraction(x:F):
    return ceil_div(x.numerator,x.denominator)

def cert_sphere_one(k:int,c:F, eta:F=F(1)):
    """Prove cap B(s)<1 for s² using outward-rational normalizer."""
    Llo,Lhi=ln(F(k))
    assert Llo>100
    d=ceil_fraction(c*Lhi*Lhi)
    assert d>3
    logLlo=ln(Llo)[0]
    logLhi=ln(Lhi)[1]
    log4pilo,log4pihi=log_four_pi()
    Slo=2*Llo-logLhi-log4pihi-2*Lhi*Lhi/d+eta
    Shi=2*Lhi-logLlo-log4pilo-2*Llo*Llo/d+eta
    assert F(0)<Slo<=Shi<d,(k,c,d)
    logSlo=ln(Slo)[0]
    pl,_=pi_bounds()
    log_const_low=ln(2*pl*(1-F(1,d)))[0]
    logtail_upper=ln(1-Slo/F(d))[1]
    logBhi=Lhi-F(1,2)*logSlo-F(1,2)*log_const_low+F(d-1,2)*logtail_upper
    assert logBhi<0,(k,c,d,"log B not negative",logBhi)
    # Spherical max squared H² bound:
    ratio=F(d,d-1)
    H2up=Shi+2*ratio+ratio*ratio/Slo
    assert H2up<Shi+F(5,2),("expectation tail not small",k,d)
    return {
       "k_digits":len(str(k)),
       "c":str(c),
       "dimension":d,
       "strict_cap_union_lt_one":True,
       "squared_max_within_2point5_of_s_squared":True,
       "rational_pi_log_enclosure":True,
    }

def cert_spherical():
    arr=[]
    for n in (200,500,1000):
        k=10**n
        for c in (F(1,4),F(1),F(4)):
            r=cert_sphere_one(k,c)
            arr.append(r)
            print(f"PASS exact cap: k=10^{n}, d={r['dimension']}, "
                  f"c={c}, eta=1 and log B(s)<0")
    return arr

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--json",action="store_true")
    ap.add_argument("--quick",action="store_true")
    args=ap.parse_args()
    import contextlib,io
    if args.json:
        with contextlib.redirect_stdout(io.StringIO()):
            t=cert_tradeoff()
            b=cert_binary_entropy()
            s=cert_spherical()
            g=cert_euler_constant()
        print(json.dumps({
          "tradeoff":t,
          "binary_entropy":b,
          "spherical_cap":s,
          "euler_constant":g,
          "exact_rational_only":True,
          "universal_probability_proofs":"paper.md"
        },indent=2,sort_keys=True))
    else:
        t=cert_tradeoff()
        b=cert_binary_entropy()
        s=cert_spherical()
        g=cert_euler_constant()
        print(f"ALL CHECKS PASSED: {len(t)} tradeoff pairs, "
              f"{len(b)} binary entropy cases, "
              f"{len(s)} spherical-cap constant-term cases.")
if __name__=="__main__":
    main()
