#!/usr/bin/env python3
"""Produce exact, Pareto-minimal operation-grammar certificates. Python stdlib only.

This producer discovers the optimal state and emits all intermediate frontiers.
A *separate* verifier checks candidate-by-candidate dominance and attainability.
No floating-point arithmetic or external optimizer is used for any decision.
"""
import json
import sys
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
from pathlib import Path


@lru_cache(maxsize=None)
def g(n):
    return F(n**n, factorial(n)) if n else F(1)


def join(a, b):
    return (a[0]+b[0],a[1]*b[1])


def product(a, b, r, s):
    h1,q1=a[:2];h2,q2=b[:2];n=r+s
    h=F(n)/(F(r)/h1+F(s)/h2)
    x=(s*h1+r*h2)/n
    return h,q1*q2*x*g(r)*g(s)/g(n)


def best_record(sets, d):
    x=sets[d]
    i=max(range(len(x)),key=lambda i:x[i][0]*x[i][1])
    h,q,op=x[i]
    return i,h*q/F(d+1)


def summarize(sets, d):
    # Return flattening into join-atoms, if every product has simplex factors.
    def visit(n,i):
        op=sets[n][i][2]
        if op[0]=='point':return [('point',)]
        _,r,a,s,b=op
        if op[0]=='join':return visit(r,a)+visit(s,b)
        left=visit(r,a);right=visit(s,b)
        if all(z[0]=='point' for z in left+right):
            return [('simplex_product',len(left)-1,len(right)-1)]
        return [('other_product',r,s)]
    i,_=best_record(sets,d)
    atom=visit(d,i)
    products={}
    for x in atom:
        if x[0]=='simplex_product':
            a,b=sorted(x[1:]);products[(a,b)]=products.get((a,b),0)+1
    return {'join_points':sum(x[0]=='point' for x in atom),
            'simplex_products':[{'p':a,'q':b,'count':c} for (a,b),c in sorted(products.items())],
            'other_product_atoms':sum(x[0]=='other_product' for x in atom)}


def main(N=48, output=None):
    sets=[[(F(1),F(1),['point'])]]
    stats=[]
    for n in range(1,N+1):
        candidates={}
        # Joins of dimensions r+s+1=n; pairs up to permutation.
        for r in range(n):
            s=n-r-1
            if r>s:break
            for i,a in enumerate(sets[r]):
                for j,b in enumerate(sets[s]):
                    h,q=join(a,b)
                    old=candidates.get(h)
                    if old is None or q>old[0]:
                        candidates[h]=(q,['join',r,i,s,j])
        # Cartesian products with both factors positive dimensional.
        for r in range(1,n):
            s=n-r
            if r>s:break
            for i,a in enumerate(sets[r]):
                for j,b in enumerate(sets[s]):
                    h,q=product(a,b,r,s)
                    old=candidates.get(h)
                    if old is None or q>old[0]:
                        candidates[h]=(q,['product',r,i,s,j])
        # Exact (coordinatewise) Pareto reduction.
        frontier=[]
        record=F(0)
        for h,(q,op) in sorted(candidates.items(),reverse=True):
            if q>record:
                frontier.append((h,q,op))
                record=q
        sets.append(frontier)
        idx,ratio=best_record(sets,n)
        sm=summarize(sets,n)
        stats.append({'dimension':n,'frontier_size':len(frontier),
                      'best_index':idx,'ratio_num':str(ratio.numerator),
                      'ratio_den':str(ratio.denominator),'optimal_structure':sm})
        if n==1 or n%4==0 or n==N:
            print(f'd={n:2} Pareto={len(frontier):4} exact R_max/c_n={ratio}; structure={sm}',flush=True)
    output=output or Path(__file__).resolve().parent.parent/'certificates'/'frontiers48.json'
    output=Path(output)
    payload={'scope':'finite point-generated product/join class modulo affine equivalence',
             'max_dimension':N,
             'states':[[{'H':str(h),'Q':str(q),'op':op} for h,q,op in frontier] for frontier in sets],
             'summary':stats}
    output.write_text(json.dumps(payload,separators=(',',':'),ensure_ascii=True)+'\n')
    print('CERTIFICATE',output,'STATES',sum(len(z) for z in sets),'BYTES',output.stat().st_size)


if __name__=='__main__':
    main(int(sys.argv[1]) if len(sys.argv)>1 else 48,
         sys.argv[2] if len(sys.argv)>2 else None)
