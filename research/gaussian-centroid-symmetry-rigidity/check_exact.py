#!/usr/bin/env python3
"""Pure Fraction algebraic verification of Gaussian centroid symmetry identities.

The checker does not claim that arbitrary rational centroid-length
profiles are realized by Gaussian partitions. The universal spherical
cap and Mills estimates are ANALYTIC theorems in paper.md.

All assertions here are exact operations on arbitrary-size integers
or Fraction. No binary floats, numerical Gaussian integration or solver.
"""
from fractions import Fraction as F
from random import Random
import argparse
import json


def check_profile(a, h, H):
    a = tuple(F(x) for x in a)
    h,H=F(h),F(H)
    k=len(a)
    assert k>=2 and 0<=H<=h
    assert all(0<=x<=h for x in a)
    mean=sum(a,F(0))/k
    assert mean<=H
    V=sum(((x-mean)**2 for x in a),F(0))/k
    P=sum((x*x for x in a),F(0))/(k*k)
    U=h*h/k
    assert k*P == mean*mean+V
    assert k*(U-P)+V == h*h-mean*mean
    assert k*(U-P)+V >= h*h-H*H
    assert V>=0
    if len(set(a))==1:
        assert V==0
    return {
        "cell_count":k,
        "exact_variance_identity":True,
        "exact_support_max_converse":True,
        "homogeneous":len(set(a))==1,
        "variance":[V.numerator,V.denominator],
    }


def run():
    rng=Random(20261007)
    profiles=[
        ("binary_hom", [F(1)]*2, F(2), F(1)),
        ("binary_split", [F(0),F(2)], F(2), F(1)),
        ("uniform_10", [F(3,2)]*10,F(2),F(3,2)),
        ("one_bad_100", [F(0)]+[F(2)]*99,F(2),F(2)),
        ("alternating_100", [F(0),F(2)]*50,F(2),F(1)),
        ("tiny_bad_fraction", [F(0)]*17+[F(11,4)]*983,F(3),F(3)),
        ("rational_unequal", [F(1,7),F(1,3),F(1,2),F(2,3)],F(1),F(1)),
    ]
    for k in (3,7,17,101,1024):
        for rep in range(2):
            h=F(3)
            a=[F(rng.randrange(0,301),100) for _ in range(k)]
            mean=sum(a,F(0))/k
            slack=F(3)-mean
            H=mean+slack/F(2)
            profiles.append((f"pseudorational_{k}_{rep}",a,h,H))
    results=[]
    for name, a, h, H in profiles:
        x=check_profile(a,h,H)
        x["name"]=name
        results.append(x)
        print(f"PASS exact centroid-variance: {name}, "
              f"k={x['cell_count']}, zero-variance={x['homogeneous']}")
    # Negative control: omitting V breaks the algebraic implication
    # whenever the norm profile is heterogeneous. This is a
    # MODEL ALGEBRA CONTROL, not a realizable Gaussian 2-cell partition.
    a=[F(0),F(2)]
    mean=F(1); h=F(2); H=mean
    P=sum((x*x for x in a),F(0))/(2*2)
    U=h*h/2
    assert 2*(U-P)<h*h-H*H
    print("PASS negative algebraic control: omitting variance can break cap transfer")
    assert all(r['exact_variance_identity'] for r in results)
    print(f"ALL EXACT CHECKS PASSED: {len(results)} rational profiles, "
          "one algebraic negative control; no floating point")
    return results


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--json",action="store_true")
    args=parser.parse_args()
    if args.json:
        import io,contextlib
        with contextlib.redirect_stdout(io.StringIO()):
            result=run()
        print(json.dumps({"cases":result,
                          "negative_control":True,
                          "universal_proof":"paper.md",
                          "arithmetic":"fractions.Fraction"},
                         sort_keys=True,indent=2))
    else:
        run()
