#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import permutations
from math import comb, factorial, prod
from pathlib import Path
import json, hashlib
from check import support_stats, require


def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    while len(c)>1 and c[-1]==0:c.pop()
    return c


def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    while len(c)>1 and c[-1]==0:c.pop()
    return c


def rank_polynomial(d,s):
    matrix=[]
    for i in range(s):
        row=[]
        for j in range(s):
            vals=[F(comb(d+q+i-j-1,d-1)) for q in range(d)]
            coeff=[]
            for ell in range(d):
                coeff.append(vals[0]/factorial(ell))
                vals=[b-a for a,b in zip(vals,vals[1:])]
            row.append(coeff)
        matrix.append(row)
    out=[F(0)]
    for perm in permutations(range(s)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(s) for j in range(i+1,s))
        term=[F(sign)]
        for i,j in enumerate(perm):term=mul(term,matrix[i][j])
        out=add(out,term)
    return out


def evaluate_rank(poly,s,k):
    return sum((coef*prod(range(k-j+1,k+1))/s**j for j,coef in enumerate(poly) if j<=k),start=F(0))*s**k


def main():
    records=[]
    count=0
    for d in range(2,7):
        for s in range(1,d+1):
            pp=rank_polynomial(d,s)
            g=s*(d-s)
            require(len(pp)-1==g,'Toeplitz determinant degree != support exponent')
            denominator=prod(j-i for i in range(s) for j in range(s,d))
            require(pp[-1]==F(1,denominator),'Toeplitz leading coefficient wrong')
            require(pp[0]==1,'empty word rank not one')
            for k in range(1,13):
                rr,_=support_stats(d,s,k)
                require(evaluate_rank(pp,s,k)==rr,'Toeplitz polynomial != independent Weyl/hook rank')
                count+=1
            records.append({'D':d,'s':s,'coefficients_of_P':[str(x) for x in pp]})
    expected=[F(1),F(2),F(2),F(2,3),F(1,12)]
    require(rank_polynomial(4,2)==expected,'D4s2 example wrong')
    expected2=[F(1),F(1),F(1,2),F(1,6)]
    require(rank_polynomial(4,3)==expected2,'D4s3 example wrong')
    wrong=rank_polynomial(4,2).copy()
    wrong[-1]*=factorial(4)
    require(evaluate_rank(wrong,2,7)!=support_stats(4,2,7)[0],'EGF coefficient factorial mutation not rejected')
    report={'status':'PASS','scope':'exact finite classical-count identities; not asymptotic or Lean proof','cases':count,'polynomials':records,'negative_control_rejected':'multiply EGF coefficient by its factorial','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=Path(__file__).parent/'verification/rank-polynomial-checks.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='polynomials'},indent=2))

if __name__=='__main__':main()
