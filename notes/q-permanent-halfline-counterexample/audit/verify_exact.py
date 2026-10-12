#!/usr/bin/env python3
"""Independent audit; Python standard library only, exact Fraction arithmetic.
No results imported from the proposer. Enumerates every permutation.
"""
from fractions import Fraction as F
from itertools import permutations, combinations
from functools import reduce
from operator import mul
from pathlib import Path
import json

A = [[F(int(i==j)) for j in range(4)] for i in range(4)]
for i,j,v in [(0,1,F(-99,100)),(0,3,F(1,500)),(1,3,F(1,8))]:
    A[i][j]=A[j][i]=v

def inv(p):
    return sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def determinant(B):
    return sum((-1)**inv(p)*reduce(mul,(B[i][p[i]] for i in range(len(B))),F(1)) for p in permutations(range(len(B))))
def submatrix(I):
    return [[A[i][j] for j in I] for i in I]

coeff=[F(0) for _ in range(7)]
rows=[]
for p in permutations(range(4)):
    product=reduce(mul,(A[i][p[i]] for i in range(4)),F(1))
    power=inv(p)
    coeff[power]+=product
    rows.append({'permutation_one_line':[x+1 for x in p],'inversions':power,'entry_product':str(product)})
assert len(rows)==24
assert coeff==[F(1),F(9801,10000),F(0),F(1,64),F(-99,200000),F(1,250000),F(0)]
leading=[determinant(submatrix(range(k))) for k in range(1,5)]
assert leading==[F(1),F(199,10000),F(199,10000),F(59,15625)]
assert all(d>0 for d in leading)
principal={','.join(str(x+1) for x in I):str(determinant(submatrix(I))) for k in range(1,5) for I in combinations(range(4),k)}
assert all(F(v)>0 for v in principal.values())
def P(x): return sum(c*x**k for k,c in enumerate(coeff))
def dP(x): return sum(k*c*x**(k-1) for k,c in enumerate(coeff) if k)
assert dP(F(50))==F(-10831,2500)
assert P(F(49))-P(F(50))==F(2117513,500000)
assert P(F(-1))==determinant(A)
assert P(F(1))==sum(reduce(mul,(A[i][p[i]] for i in range(4)),F(1)) for p in permutations(range(4)))
# Uniform derivative lower bound on [-1,1]: drop nonnegative even-power terms.
lower=coeff[1]-abs(4*coeff[4])
assert lower==F(48906,50000)>0
result={'matrix':[[str(x) for x in r] for r in A], 'all_24_permutations':rows, 'coefficients_ascending':[str(c) for c in coeff], 'leading_principal_minors':[str(d) for d in leading], 'all_principal_minors':principal,'P(-1)':str(P(F(-1))),'P(1)':str(P(F(1))), 'P(49)':str(P(F(49))),'P(50)':str(P(F(50))),'P(49)-P(50)':str(P(F(49))-P(F(50))),'Pprime(50)':str(dP(F(50))),'Pprime_lower_bound_on_[-1,1]':str(lower),'verdict':'All exact assertions pass. Real symmetric strictly positive definite, non-diagonal. Strict monotonicity fails at 49 < 50, both in every (epsilon,infinity) with epsilon <= -1. This example is strictly increasing on [-1,1].'}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
