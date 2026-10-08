#!/usr/bin/env python3
"""Exact integer/rational certificates for Gaussian dimension-rate proofs.

Theorems involving Gaussian calculus, entropy, and asymptotic
expectations are proved analytically in paper.md. This program
checks finite-balanced-tree combinatorics, outward-rational
logarithmic bounds for the explicit b-ary energy constants,
and rational exponential bounds for dimension converse
curves. It uses no floating-point operations or solver.
"""
from fractions import Fraction as F
from functools import lru_cache
import argparse
import json

SCALE=10**85

def ceil_div(a:int,b:int)->int:
    assert b>0
    return -((-a)//b)

def atanh_bounds(z:F,N:int=92):
    """Outward fixed-point enclosure of 2 atanh(z), 0<=z<=1/3."""
    assert 0<=z<=F(1,3)
    lo=z.numerator*SCALE//z.denominator
    hi=ceil_div(z.numerator*SCALE,z.denominator)
    assert hi*hi<SCALE*SCALE
    p_lo,p_hi=lo,hi
    L=R=0
    for n in range(N):
        den=2*n+1
        L+=(2*p_lo)//den
        R+=ceil_div(2*p_hi,den)
        p_lo=p_lo*lo*lo//(SCALE*SCALE)
        p_hi=ceil_div(p_hi*hi*hi,SCALE*SCALE)
    tail=ceil_div(2*p_hi*SCALE*SCALE,
                  (2*N+1)*(SCALE*SCALE-hi*hi))
    return F(L,SCALE),F(R+tail,SCALE)

@lru_cache(maxsize=1)
def log2_bounds():
    return atanh_bounds(F(1,3))

@lru_cache(maxsize=10000)
def log_bounds(x:F):
    assert x>0
    if x==1:return F(0),F(0)
    e=x.numerator.bit_length()-x.denominator.bit_length()
    m=x/F(2)**e
    while m<1:m*=2;e-=1
    while m>=2:m/=2;e+=1
    z=(m-1)/(m+1)
    a,b=atanh_bounds(z)
    c,d=log2_bounds()
    return ((a+e*c,b+e*d) if e>=0 else (a+e*d,b+e*c))

def loglog_bounds(x:F):
    """Certified enclosure of log(log(x)), for x>e."""
    l,u=log_bounds(x)
    assert l>1
    return log_bounds(l)[0],log_bounds(u)[1]

def cert_energy(b:int):
    """Exact rational enclosure of L_b/(2 log b)."""
    assert b>=2
    la,lb=log_bounds(F(b,2))
    ca,cb=loglog_bounds(F(2*b))
    ba,bb=log_bounds(F(b))
    lo=2*la-cb-6
    hi=2*lb-ca-6
    return lo/(2*bb),hi/(2*ba),lo,hi

def balanced_tree(k:int,b:int):
    assert k>=2 and b>=2
    nodes=[k]
    stages=[]
    while any(m>1 for m in nodes):
        nt=[]
        regular=0
        previous_nodes=len(nodes)
        premature_terminal=0
        for m in nodes:
            if m==1:
                premature_terminal+=1
                nt.append(1)
                continue
            r=min(b,m)
            q,rem=divmod(m,r)
            sizes=[q+1]*rem+[q]*(r-rem)
            assert sum(sizes)==m and min(sizes)>0
            if r==b:
                assert all(F(1,2*b)<=F(x,m)<=F(2,b) for x in sizes)
                regular+=1
            for j,v in enumerate(sizes):
                # Exact conditional-mass telescoping on each edge:
                # parent probability m/k times child mass v/m = v/k.
                assert F(m,k)*F(v,m)==F(v,k)
            nt.extend(sizes)
        assert sum(nt)==k
        nodes=nt
        stages.append((len(nodes),regular,previous_nodes,premature_terminal))
        assert len(stages)<=100
    T=len(stages)
    expect=0
    power=1
    while power<k:
        power*=b
        expect+=1
    assert expect==T,(k,b,T,expect)
    assert len(nodes)==k and all(m==1 for m in nodes)
    assert all(regular==previous_nodes and terminals==0
               for _,regular,previous_nodes,terminals
               in stages[:max(0,T-1)])
    return T,len(nodes),stages

def exp_positive_bounds(x:F,terms:int=100):
    assert F(0)<=x<=F(2)
    p=F(1)
    result=F(1)
    for j in range(1,terms):
        p=p*x/j
        result+=p
    next_term=p*x/terms
    ratio=x/(terms+1)
    assert ratio<F(1)
    return result,result+next_term/(1-ratio)

def exp_minus_bounds(x:F):
    a,b=exp_positive_bounds(x)
    return 1/b,1/a

def fcurve_bounds(c:F):
    assert c>=1
    lo,hi=exp_minus_bounds(F(2)/c)
    return c*(1-hi)/2,c*(1-lo)/2

def run(quick:bool,verbose:bool=True):
    checks=[]
    examples=[
        (2,2),(3,2),(7,2),(8,2),(9,2),(10,3),
        (11,3),(17,4),(64,4),(65,4),(256,7),
        (257,7),(1000,10),(1001,10),(2026,13)]
    if not quick:
        examples +=[(4097,16),(65537,24),(100003,31)]
    for k,b in examples:
        T,leaves,steps=balanced_tree(k,b)
        checks.append({"k":k,"arity":b,"depth":T,
                       "dimension_bound":(b-1)*T,
                       "equal_mass_leaves":leaves,
                       "complete_balancing":True})
        if verbose:
            print(f"PASS balanced tree: k={k}, b={b}, "
                  f"T={T}, d<={(b-1)*T}, {leaves} exact equal-mass leaves")

    # Each certificate uses a finite but possibly astronomically
    # large integer b. No tree of that size is enumerated.
    tolerances=[
        (F(1,2),10),
        (F(1,5),30),
        (F(1,10),60),
        (F(1,20),140),
    ]
    if quick:tolerances=tolerances[:2]
    large=[]
    for eps,pow10 in tolerances:
        b=10**pow10
        ratio_lo,ratio_hi,Llo,Lhi=cert_energy(b)
        assert Llo>0 and ratio_lo>=1-eps/2,(eps,pow10,ratio_lo)
        power=2*eps.denominator//eps.numerator
        if power*eps.numerator<2*eps.denominator:power+=1
        # k=b^T, with T>=2/eps; the rational relative guarantee
        # is >= (L_b/(2 log b)) * (1 - 1/T).
        guaranteed=ratio_lo*(1-F(1,power))
        assert guaranteed>=1-eps,(eps,guaranteed)
        large.append({"epsilon":str(eps),"b":"10^"+str(pow10),
                      "min_k":"b^"+str(power),
                      "local_ratio_lower":str(ratio_lo),
                      "global_ratio_lower":str(guaranteed)})
        if verbose:
            print(f"PASS rational dimension-rate witness: eps={eps}, "
                  f"b=10^{pow10}, T>={power}, relative guarantee >=1-eps")

    for c,eps,expected in [
        (F(2),F(1,10),False),
        (F(9),F(1,10),False),
        (F(10),F(1,10),True),
        (F(19),F(1,20),False),
        (F(20),F(1,20),True)]:
        lo,hi=fcurve_bounds(c)
        if expected:
            assert lo>1-eps,(c,lo)
        else:
            assert hi<1-eps,(c,hi)
        if verbose:
            print(f"PASS entropy converse root bracket: "
                  f"f({c}) {'>' if expected else '<'} {1-eps}")
    if verbose:
        print(f"ALL EXACT CHECKS PASS: {len(checks)} balanced trees, "
              f"{len(large)} certified large-branch constructions, "
              "5 rate-distortion inequality controls.")
    return {"balanced_cases":checks,"large_branch_certificates":large,
            "rate_distortion_controls":5,
            "exact_integer_arithmetic":True,
            "full_universal_proofs_in":"paper.md"}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--quick",action="store_true")
    ap.add_argument("--json",action="store_true")
    args=ap.parse_args()
    report=run(args.quick,verbose=not args.json)
    if args.json:
        print(json.dumps(report,sort_keys=True,indent=2))

if __name__=="__main__":
    main()
