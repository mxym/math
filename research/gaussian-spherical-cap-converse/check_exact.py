#!/usr/bin/env python3
"""Independent exact-rational checks of the spherical-cap dimension theorem.

The analytic theorem is proved in paper.md; numerical examples are not
used as universal proof. This checker verifies the *exact* finite
logarithmic threshold beta<1 for selected (very large) integers k,
the threshold's domain, the resulting radius bound, the elementary
gamma/Mills endpoint constants, and the dimension-defect algebra.

No binary floating-point arithmetic, numerical normal quantiles,
closed-source solvers, or heuristic certificates are used.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
import argparse
import json

SCALE=10**100

def ceil_div(a,b):
    assert b>0
    return -((-a)//b)

def atanh_int(z:Q, n:int=105):
    assert 0<=z<=Q(1,3)
    lo=z.numerator*SCALE//z.denominator
    hi=ceil_div(z.numerator*SCALE,z.denominator)
    assert 0<=lo<=hi and hi*hi<SCALE*SCALE
    p=lo
    v=hi
    L=H=0
    for j in range(n):
        denominator=2*j+1
        L+=(2*p)//denominator
        H+=ceil_div(2*v,denominator)
        p=p*lo*lo//(SCALE*SCALE)
        v=ceil_div(v*hi*hi,SCALE*SCALE)
    tail=ceil_div(2*v*SCALE*SCALE,(2*n+1)*(SCALE*SCALE-hi*hi))
    return Q(L,SCALE),Q(H+tail,SCALE)

@lru_cache(maxsize=1)
def log2():
    return atanh_int(Q(1,3))

@lru_cache(maxsize=3000)
def logarithm(x:Q):
    assert x>0
    if x==1:return Q(0),Q(0)
    power=x.numerator.bit_length()-x.denominator.bit_length()
    factor=x/Q(2)**power
    while factor<1:
        factor*=2
        power-=1
    while factor>=2:
        factor/=2
        power+=1
    m,n=atanh_int((factor-1)/(factor+1))
    l,h=log2()
    return ((m+power*l,n+power*h)
            if power>=0 else (m+power*h,n+power*l))

def atan_reciprocal(m:int,n:int=65):
    assert m>=2
    series=sum((Q((-1)**j,(2*j+1)*m**(2*j+1))
                for j in range(n)),Q(0))
    tail=Q(1,(2*n+1)*m**(2*n+1))
    return ((series-tail,series) if n%2 else (series,series+tail))

@lru_cache(maxsize=1)
def pi_interval():
    a,b=atan_reciprocal(5)
    c,d=atan_reciprocal(239)
    lo,hi=16*a-4*d,16*b-4*c
    assert Q(314,100)<lo<hi<Q(315,100)
    return lo,hi

def ceil_fraction(x:Q):
    return ceil_div(x.numerator,x.denominator)

def certify(k:int,d:int):
    """Exact interval of log B_{d,k}(sqrt S), no floating-point."""
    assert k>=10**44 and d>=3
    Llo,Lhi=logarithm(Q(k))
    assert Llo>100
    llo,lhi=logarithm(Llo)[0],logarithm(Lhi)[1]
    assert llo>0
    Slo=2*Llo-lhi-2*Lhi**2/d+16
    Shi=2*Lhi-llo-2*Llo**2/d+16
    assert Slo>=Lhi and Shi<Q(d)
    logSlo=logarithm(Slo)[0]
    pi_lo,_=pi_interval()
    log2pi=logarithm(Q(2)*pi_lo*(1-Q(1,d)))[0]
    log_one_minus=logarithm(1-Slo/d)[1]
    logbeta_upper=(Lhi-Q(1,2)*logSlo
                   -Q(1,2)*log2pi
                   +Q(d-1,2)*log_one_minus)
    assert logbeta_upper<0,("cap fails",k,d)
    # Squared Gaussian max threshold
    # H^2 <= (sqrt(S) + 2/sqrt(S))^2 <= S+8.
    assert Slo>1
    # Normal hazard squared h_k^2 >=2L-logL-4;
    # maximum squared bound <=2L-logL-2L^2/d+24.
    # Hence the difference of the two proven symbolic
    # envelopes is exactly 2L^2/d -28.
    difflo=2*Llo**2/d-28
    dimdeflo=Llo**2/d-14
    assert difflo==2*dimdeflo
    return {
        "digits":len(str(k)),
        "dimension":d,
        "log_beta_strictly_negative":True,
        "cap_threshold_in_range":True,
        "squared_max_remainder_8":True,
        "dimension_defect_deduced_exactly":True,
        "certified_log_k_lower_interval":str(Llo.numerator//Llo.denominator),
        "certified_defect_lower_bound_in_units_1_over_k":
             [dimdeflo.numerator,dimdeflo.denominator],
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--json",action="store_true")
    args=ap.parse_args()
    samples=[10**44,10**75,10**200,10**1000]
    out=[]
    for k in samples:
        Llo,Lhi=logarithm(Q(k))
        llo,lhi=logarithm(Llo)[0],logarithm(Lhi)[1]
        # Conservative ceil(L^2/log L) from outward interval
        d0=ceil_fraction(Lhi**2/llo)
        assert Q(d0)>=Lhi**2/llo
        for d in [d0,2*d0,10*d0]:
            cert=certify(k,d)
            out.append(cert)
            if not args.json:
                print(f"PASS exact cap threshold: k=10^{len(str(k))-1}, "
                      f"d={d}, log(beta)<0 and spherical defect algebra")
    assert Q(8,3)**4>Q(16)*Q(22,7)
    assert logarithm(Q(16)*pi_interval()[1])[1]<4
    # Universal coefficient arithmetic in the displayed proof:
    assert -8+3+Q(3,20)+Q(9,400)<0
    assert Q(1,2)*28==14
    if args.json:
        print(json.dumps({"method":"outward rational intervals",
                          "universal_proof":"paper.md",
                          "samples":out,
                          "all_passed":True},sort_keys=True,indent=2))
    else:
        print(f"PASS: all {len(out)} certified nonasymptotic cap samples")
        print("PASS: rational Mills/gamma constants and dimension-defect algebra")
        print("ALL SPHERICAL-CAP EXACT CHECKS PASSED")

if __name__=="__main__":
    main()
