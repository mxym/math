#!/usr/bin/env python3
"""Proof-interface checker for cyclic Gaussian orbit frequencies.

All verified coherence comparisons use exact rational enclosures for
pi, cos(2*pi*j/k), log(k) and 1/log(k). No floating point is involved.
The frequency lists may have been found by a seeded search: their
validity is established separately by this deterministic checker.

The universal existence theorem does not rely on these finite lists;
its analytic union-bound proof is in paper.md.
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path
import argparse
import json
import random

from check_exact import log_bounds, ceil_div

BASE=Path(__file__).parent
SCALE=10**70
NUM_TERMS=36

def floor_scaled(q:F)->int:
    return q.numerator*SCALE//q.denominator

def ceil_scaled(q:F)->int:
    return ceil_div(q.numerator*SCALE,q.denominator)

def atan_recip_bounds(m:int, n:int=55):
    assert m>=2
    summand=F(0)
    for j in range(n):
        summand+=F((-1)**j,(2*j+1)*m**(2*j+1))
    rem=F(1,(2*n+1)*m**(2*n+1))
    return (summand-rem,summand) if n%2 else (summand,summand+rem)

@lru_cache(maxsize=1)
def pi_bounds():
    a,b=atan_recip_bounds(5)
    c,d=atan_recip_bounds(239)
    lo,hi=16*a-4*d,16*b-4*c
    assert F(314,100)<lo<hi<F(315,100)
    return lo,hi

@lru_cache(maxsize=10000)
def cosine_scaled(k:int, j:int):
    """Rigorous signed fixed-point interval enclosing cos(2*pi*j/k)."""
    j%=k
    j=min(j,k-j)
    assert 0<=j<=k//2
    if j==0:return SCALE,SCALE
    plo,phi=pi_bounds()
    xl=floor_scaled(F(2*j,k)*plo)
    xu=ceil_scaled(F(2*j,k)*phi)
    assert 0<=xl<=xu<=ceil_scaled(phi)
    lower=upper=SCALE
    pl=pu=SCALE
    for n in range(1,NUM_TERMS):
        pl=pl*xl*xl//(SCALE*SCALE)
        pu=ceil_div(pu*xu*xu,SCALE*SCALE)
        tl=pl//factorial(2*n)
        tu=ceil_div(pu,factorial(2*n))
        if n%2:
            lower-=tu
            upper-=tl
        else:
            lower+=tl
            upper+=tu
    pu=ceil_div(pu*xu*xu,SCALE*SCALE)
    rem=ceil_div(pu,factorial(2*NUM_TERMS))
    lo=lower-rem
    hi=upper+rem
    assert lo<=hi
    return max(lo,-SCALE),min(hi,SCALE)

def ceil_q(x:F):
    return ceil_div(x.numerator,x.denominator)

def expected_m(k:int):
    lo,hi=log_bounds(F(k))
    assert lo>1
    m0=ceil_q(4*lo**3)
    m1=ceil_q(4*hi**3)
    assert m0==m1,("insufficient log interval to pin m",k,m0,m1)
    return m0,lo,hi

def verify_freqs(k:int, freqs:list[int]):
    m,ll,lh=expected_m(k)
    assert len(freqs)==m and all(type(a)==int and 0<=a<k for a in freqs)
    # One-sided upper covariance bound is all that Sudakov--Fernique needs.
    threshold_lower=1/lh
    highest=F(-1)
    for s in range(1,k):
        bound=sum(cosine_scaled(k,(s*a)%k)[1] for a in freqs)
        corr_hi=F(bound,m*SCALE)
        highest=max(highest,corr_hi)
        assert corr_hi<threshold_lower,(k,s,"covariance exceeded",str(corr_hi))
    return {
        "k":k,
        "m":m,
        "d":2*m,
        "frequency_count":len(freqs),
        "threshold_proved_strictly":True,
        "max_covariance_upper_lt_1_over_log_k":True,
        "rational_arithmetic_only":True,
    }

def generate(k:int,max_seeds:int=30):
    m,_,_=expected_m(k)
    for seed in range(max_seeds):
        rng=random.Random(20261007+123*k+seed)
        freqs=[rng.randrange(k) for _ in range(m)]
        try:
            summary=verify_freqs(k,freqs)
            return {
                "description":"Fixed cyclic frequencies, independently rationally certified",
                "seed":20261007+123*k+seed,
                "frequencies":freqs,
                "summary":summary,
            }
        except AssertionError:
            pass
    raise AssertionError(f"no certificate generated in {max_seeds} trial seeds for k={k}")

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--generate",action="store_true",
                    help="Generate and exactly verify the bundled frequency lists")
    ap.add_argument("--quick",action="store_true")
    args=ap.parse_args()
    cases=[17] if args.quick else [17,101,257]
    (BASE/"certificates").mkdir(exist_ok=True)
    for k in cases:
        path=BASE/"certificates"/f"cyclic-k{k}.json"
        if args.generate:
            payload=generate(k)
            path.write_text(json.dumps(payload,indent=2,sort_keys=True)+"\n")
        else:
            payload=json.loads(path.read_text())
        result=verify_freqs(k,payload["frequencies"])
        assert result==payload["summary"],(k,result)
        print(f"PASS exact rational orbit certificate: "
              f"k={k}, m={result['m']}, d={result['d']}, "
              "all k-1 covariance upper bounds below 1/log(k)")
    print(f"ALL CYCLIC CERTIFICATES VERIFIED: {len(cases)} samples; "
          "zero floating-point comparisons")

if __name__=="__main__":
    main()
