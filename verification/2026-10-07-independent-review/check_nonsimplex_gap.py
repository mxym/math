#!/usr/bin/env python3
"""Exact arithmetic for the FHLX section-construction comparison.

Geometric dependencies: Feng, Hu, Liu, Xu, On the Reverse Projection
Inequality, Proposition 4.1, Lemma 4.3 and equation (4.19).
This does not claim an explicit rational-vertex realization of the body
whose existence is provided by Minkowski's theorem.
"""
from fractions import Fraction as Q
from math import factorial, comb
from pathlib import Path
import json
import argparse

def require(ok, message):
    if not ok:
        raise ArithmeticError(message)

def rec(x):
    return {"numerator":str(x.numerator),"denominator":str(x.denominator)}

epsilon = Q(1,1000)
mu = Q(2,factorial(9))*sum((-1)**k*comb(8,k)*(4-k)**9 for k in range(5))
require(mu == Q(1487,2268), "absolute Irwin-Hall moment")
a = [Q(-1)] + [epsilon*j for j in range(-4,5)] + [Q(1)] + [Q(0)]*4
require(len(a)==15 and sum(a)==0, "13-dimensional section data")
D = sum(abs(x-y) for i,x in enumerate(a) for y in a[i+1:])
require(D==28+200*epsilon, "pairwise distance sum")
I_lower = 1-9*epsilon*mu
gain = D*7*I_lower/Q(14**2)
require(gain==Q(11774111,11760000)>1, "strict gain")
c13 = Q(14*13**13,factorial(13))
lower_root = Q("2.810223952012")
upper_root = Q("2.810223952013")
require(lower_root**13 < c13*gain < upper_root**13, "rational root isolation")
result={
    "status":"PASS",
    "epsilon":rec(epsilon),
    "absolute_moment":rec(mu),
    "dimension":13,
    "at_most_facets":15,
    "R13_over_c13_lower_bound":rec(gain),
    "positive_integer_margin":str(gain.numerator-gain.denominator),
    "guaranteed_rate_is_larger_than":"2.810223952012",
    "root_of_lower_bound_interval":[str(lower_root),str(upper_root)],
    "source":"https://archive.ymsc.tsinghua.edu.cn/pacm_download/743/12781--2026.8.26.pdf",
    "scope":"Arithmetic for a lower bound derived from the cited geometric existence construction; not an exact optimizer or new unrestricted upper theorem."
}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'results/nonsimplex_gap.json')
args=parser.parse_args()
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
