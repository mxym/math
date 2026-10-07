#!/usr/bin/env python3
"""Fixed rational examples; unordered subset sums, Gaussian elimination.

This generates finite consistency data, not a proof of the analytic theorems.
Run check.py separately; that checker imports none of this implementation.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import factorial, prod
from pathlib import Path


def determinant(columns):
    n = len(columns)
    rows = [[F(columns[j][i]) for j in range(n)] for i in range(n)]
    answer = F(1)
    for k in range(n):
        pivot = next((i for i in range(k, n) if rows[i][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            rows[k], rows[pivot] = rows[pivot], rows[k]
            answer = -answer
        q = rows[k][k]
        answer *= q
        for i in range(k + 1, n):
            t = rows[i][k] / q
            for j in range(k + 1, n):
                rows[i][j] -= t * rows[k][j]
    return answer


def examples():
    laws = []
    def add(name, xs, ps=None, **extra):
        xs = [tuple(map(F, x)) for x in xs]
        ps = list(map(F, ps)) if ps is not None else [F(1, len(xs))] * len(xs)
        if len(set(xs)) != len(xs) or sum(ps) != 1:
            raise ValueError('invalid fixed producer input')
        laws.append(dict(name=name, d=len(xs[0]), xs=xs, ps=ps, **extra))
    for d in range(1, 5):
        basis = [tuple(F(i == j) for j in range(d)) for i in range(d)]
        xs = basis + [(-F(1),) * d]
        add(f'uniform-simplex-d{d}', xs)
        denominator = (d + 1) * (d + 2) // 2
        ps = [F(i, denominator) for i in range(1, d + 2)]
        nonuniform = basis + [tuple(-F(i, d + 1) for i in range(1, d + 1))]
        add(f'nonuniform-simplex-d{d}', nonuniform, ps)
        if d <= 3:
            for t in (F(1, 2), F(1, 7)):
                add(f'simplex-origin-mixture-d{d}-t{t.numerator}_{t.denominator}',
                    xs + [(F(0),) * d], [t / (d + 1)] * (d + 1) + [1-t],
                    expected_ratio=F(d + 1) - d*t, expect_singular_all=True)
    for d in (2, 3):
        axes = [tuple(F(s if i == j else 0) for j in range(d))
                for i in range(d) for s in (-1, 1)]
        slabs = [tuple(F(i == j) for j in range(d)) for i in range(d)]
        add(f'axes-boundary-d{d}', axes, slabs=slabs, expected_a=F(1, 2))
        add(f'cube-vertices-boundary-d{d}', list(product((-1, 1), repeat=d)), slabs=slabs)
        add(f'even-interior-counterexample-d{d}', axes + [(F(0),)*d],
            [F(1, 4*d)]*(2*d)+[F(1, 2)], expected_a=F(3, 4),
            interior_counterexample=True)
    half = [(1, 0), (1, 1), (0, 1), (-1, 1)]
    add('nonuniform-square-boundary', half + [tuple(-q for q in x) for x in half],
        [F(i, 20) for i in (1,2,3,4,1,2,3,4)], slabs=[(1,0),(0,1)], expected_a=F(1,2))
    for d, raw in [(2, [(0,0),(2,0),(0,3),(2,2),(1,-1)]),
                   (3, [(0,0,0),(2,0,0),(0,3,0),(0,0,4),(2,2,1),(-1,1,2)])]:
        ps = [F(i+1, len(raw)*(len(raw)+1)//2) for i in range(len(raw))]
        mean = [sum(p*F(x[j]) for p,x in zip(ps,raw)) for j in range(d)]
        add(f'centered-generic-d{d}', [[F(x[j])-mean[j] for j in range(d)] for x in raw], ps)
    return laws


def make_case(law):
    d, xs, ps = law['d'], law['xs'], law['ps']
    ws = [x+(F(1),) for x in xs]
    A = factorial(d)*sum((abs(determinant([xs[i] for i in I]))*prod(ps[i] for i in I)
                         for I in combinations(range(len(xs)), d)), F(0))
    B = factorial(d+1)*sum((abs(determinant([ws[i] for i in I]))*prod(ps[i] for i in I)
                           for I in combinations(range(len(xs)), d+1)), F(0))
    singular, witness = F(0), None
    for I in combinations(range(len(xs)), d):
        fs = [determinant([ws[i] for i in I]+[w]) for w in ws]
        plus = [(j,f) for j,f in enumerate(fs) if f>0]
        minus = [(j,-f) for j,f in enumerate(fs) if f<0]
        if not determinant([xs[i] for i in I]):
            singular += factorial(d)*prod(ps[i] for i in I)*sum(p*abs(f) for p,f in zip(ps,fs))
        if witness is None and plus and minus:
            p,dp = plus[0]; q,dq = minus[0]
            bound = 2*factorial(d)*prod(ps[i] for i in I)*min(ps[p]*dp, ps[q]*dq)
            witness = dict(base=list(I), plus=p, minus=q, plus_det=str(dp),
                           minus_det=str(dq), bound=str(bound))
    output = dict(name=law['name'], dimension=d,
                  points=[[str(x) for x in row] for row in xs], weights=list(map(str,ps)),
                  expected=dict(A=str(A), B=str(B), defect=str(B-A),
                                singular_defect=str(singular), lower_equality=(B==A),
                                normalized_a=str(B/((d+1)*A))))
    if 'slabs' in law:
        output['symmetric_boundary_slabs'] = [[str(F(x)) for x in row] for row in law['slabs']]
    for key in ('expected_ratio','expected_a'):
        if key in law:
            output[key] = str(law[key])
    for key in ('expect_singular_all','interior_counterexample'):
        if law.get(key): output[key] = True
    if witness: output['strictness_witness'] = witness
    return output


def spectral_examples():
    def g(n):
        return F(n**n, factorial(n))
    seeds = [('simplex', 1, F(1,2), F(2), 2),
             ('simplex', 4, F(1,5), F(160,3), 1),
             ('cube', 3, F(1,2), F(8), 5),
             ('octahedron', 3, F(15,32), F(9), 4),
             ('two-four-simplices', 8, F(1,5), F(160,3)**2, 2)]
    out=[]
    for kind,d,a,R,k in seeds:
        N=k*(d+1)-1
        Q=a*R/g(d)
        RJ=g(N)*F(k)/a*Q**k
        aj=a/k
        QL=aj*RJ**2/g(2*N)
        threshold=F(k)**(d+1)*Q**2/(4*a*a*(d+1))**(d+1)
        improvement=QL**(d+1)/Q**(2*N+1)
        if threshold<1 or improvement<=1:
            raise ValueError('fixed seed does not meet square-amplification test')
        out.append(dict(kind=kind,seed_dimension=d,seed_a=str(a),seed_R=str(R),seed_Q=str(Q),
                        joins=k,final_dimension=2*N,final_Q=str(QL),
                        threshold_ratio=str(threshold),improvement_ratio=str(improvement)))
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('certificates/exact.json'))
    args = parser.parse_args()
    data = dict(schema='005-v3-random-determinants-1', cases=[make_case(x) for x in examples()],
                spectral_examples=spectral_examples())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')
    print(f'Wrote {len(data["cases"])} fixed rational laws to {args.output}')

if __name__ == '__main__': main()
