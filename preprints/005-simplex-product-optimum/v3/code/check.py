#!/usr/bin/env python3
"""Independent exact finite checker. No producer imports and no floating point.

Ordered tuples and the Leibniz determinant are used independently of generate.py.
The manuscript, not these finite checks, proves the general statements.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations, product
import json
from math import comb, factorial, prod
from pathlib import Path


def need(condition, message):
    if not condition:
        raise ValueError(message)


def rational(x):
    need(isinstance(x, str), 'rational data must use strings, not floats')
    return F(x)


@lru_cache(None)
def signs(n):
    return tuple((p, (-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)))
                 for p in permutations(range(n)))


@lru_cache(None)
def det(cols):
    n = len(cols)
    need(all(len(col)==n for col in cols), 'nonsquare determinant')
    if len(set(cols)) < n:
        return F(0)
    answer = F(0)
    for p,s in signs(n):
        term = F(s)
        for j in range(n):
            term *= cols[j][p[j]]
            if not term: break
        answer += term
    return answer


def check_case(case):
    d = case['dimension']
    need(isinstance(d,int) and not isinstance(d,bool) and 1<=d<=5, 'invalid checker dimension')
    xs = tuple(tuple(map(rational,row)) for row in case['points'])
    ps = tuple(map(rational,case['weights']))
    N = len(xs)
    need(N==len(ps) and N>=d+1 and all(len(x)==d for x in xs), 'shape mismatch')
    need(len(set(xs))==N and all(p>0 for p in ps) and sum(ps)==1, 'invalid probability law')
    need(all(sum(p*x[j] for p,x in zip(ps,xs))==0 for j in range(d)), 'law is not centered')
    ws = tuple(x+(F(1),) for x in xs)
    A=B=defect=singular=F(0)
    ordered_count=0
    for I in product(range(N),repeat=d):
        probability = prod(ps[i] for i in I)
        D = det(tuple(xs[i] for i in I))
        pos=neg=F(0)
        for j in range(N):
            value = det(tuple(ws[i] for i in I)+(ws[j],))
            if value>0: pos += ps[j]*value
            elif value<0: neg -= ps[j]*value
            ordered_count += 1
        need(pos-neg==D, 'conditional centering/determinant identity failed')
        A += probability*abs(D)
        B += probability*(pos+neg)
        contribution = 2*probability*min(pos,neg)
        defect += contribution
        if D==0: singular += contribution
    need(A>0,'law does not span the ambient space')
    need(A<=B<(d+1)*A,'random determinant inequality failed')
    need(B-A==defect,'complete cancellation identity failed')
    simplex = N==d+1 and det(ws)!=0
    need((B==A)==simplex,'equality classification disagrees with exact data')
    expected = case['expected']
    for key,value in [('A',A),('B',B),('defect',defect),('singular_defect',singular),
                      ('normalized_a',B/((d+1)*A))]:
        need(rational(expected[key])==value, f'{case["name"]}: wrong {key}')
    need(isinstance(expected['lower_equality'],bool) and expected['lower_equality']==simplex,
         'wrong lower-equality flag')
    if 'expected_ratio' in case: need(B/A==rational(case['expected_ratio']),'mixture ratio failed')
    if 'expected_a' in case: need(B/((d+1)*A)==rational(case['expected_a']),'stated a failed')
    if case.get('expect_singular_all'):
        need(singular==defect and defect>0,'singular-tuples-only defect not verified')
    lookup = dict(zip(xs,ps))
    even = all(lookup.get(tuple(-z for z in x))==p for x,p in zip(xs,ps))
    if 'symmetric_boundary_slabs' in case:
        need(even,'claimed boundary law is not even')
        slabs = tuple(tuple(map(rational,row)) for row in case['symmetric_boundary_slabs'])
        need(len(slabs)>=d and all(len(row)==d for row in slabs),'invalid norm slabs')
        need(any(det(tuple(rows))!=0 for rows in combinations(slabs,d)),'norm slabs do not bound a body')
        for x in xs:
            gauge = max(abs(sum(a*b for a,b in zip(row,x))) for row in slabs)
            need(gauge==1,'law is not supported on the certified boundary')
        need(2*B<=(d+1)*A,'symmetric boundary upper bound failed')
        if d==2: need(2*B==3*A,'planar constancy failed')
    if case.get('interior_counterexample'):
        need(even and (F(0),)*d in lookup,'missing even interior atom example')
        need(2*B>(d+1)*A,'not a counterexample to removing the boundary hypothesis')
    witness = case.get('strictness_witness')
    if not simplex:
        need(isinstance(witness,dict),'strict case lacks a finite sign witness')
        I = witness['base']; p=witness['plus']; q=witness['minus']
        need(len(I)==d and len(set(I+[p,q]))==d+2,'witness atoms are not distinct')
        need(all(isinstance(i,int) and 0<=i<N for i in I+[p,q]),'invalid witness index')
        dp = det(tuple(ws[i] for i in I)+(ws[p],))
        dm = -det(tuple(ws[i] for i in I)+(ws[q],))
        need(dp>0 and dm>0,'witness does not change determinant sign')
        bound = 2*factorial(d)*prod(ps[i] for i in I)*min(ps[p]*dp,ps[q]*dm)
        need(dp==rational(witness['plus_det']) and dm==rational(witness['minus_det']),
             'wrong witness determinants')
        need(bound==rational(witness['bound']) and 0<bound<=defect,'wrong strictness lower bound')
    else:
        need(witness is None,'simplex unexpectedly supplied a strict witness')
    return dict(name=case['name'],dimension=d,atoms=N,A=str(A),B=str(B),
                normalized_a=str(B/((d+1)*A)),defect=str(defect),
                singular_defect=str(singular),simplex_equality=simplex,
                ordered_lifted_tuples=ordered_count)


def rademacher_tests():
    count=0
    for n in range(2,6):
        for cs in product(range(4),repeat=n):
            total=sum(cs)
            if total==0 or 2*max(cs)>total: continue
            sign_sum=sum(abs(sum(c*s for c,s in zip(cs,eps))) for eps in product((-1,1),repeat=n))
            need(sign_sum<=(2**(n-1))*total,'balanced sign average failed')
            if n in (2,3): need(sign_sum==(2**(n-1))*total,'low-dimensional identity failed')
            count += 1
    return count


def octahedron_geometry():
    # Direct facet-minor oracle for O_3, independent of probability enumeration.
    facets=tuple((tuple(F(e,2) for e in eps), F(1,2))
                 for eps in product((-1,1),repeat=3))
    volume=F(4,3)
    P=sum((abs(det(tuple(row[0] for row in subset)))
           for subset in combinations(facets,3)),F(0))
    S=sum((abs(det(tuple(row[0]+(row[1],) for row in subset)))
           for subset in combinations(facets,4)),F(0))
    R=P/volume**2; a=S/(3*volume*P)
    need(P==16 and S==30 and R==9 and a==F(15,32),'direct octahedron geometry failed')
    return dict(volume=str(volume),P=str(P),S=str(S),R=str(R),a=str(a),
                horizontal_minors=56,lifted_minors=70)


def check_spectral(example):
    d,k = (example[key] for key in ('seed_dimension','joins'))
    need(all(isinstance(n,int) and not isinstance(n,bool) and n>=1 for n in (d,k)),
         'invalid spectral recipe')
    kind=example['kind']
    if kind=='simplex':
        a=F(1,d+1); R=F((d+1)*d**d,factorial(d))
    elif kind=='cube':
        a=F(1,2); R=F(2**d)
    elif kind=='octahedron':
        need(d==3,'octahedron seed has wrong dimension')
        geometry=octahedron_geometry(); a=F(geometry['a']); R=F(geometry['R'])
    elif kind=='two-four-simplices':
        need(d==8,'simplex-product seed has wrong dimension')
        a=F(1,5); R=F(160,3)**2
    else:
        raise ValueError('unknown geometric seed')
    Q=a*R*F(factorial(d),d**d)
    need(a==rational(example['seed_a']) and R==rational(example['seed_R'])
         and Q==rational(example['seed_Q']),'seed values disagree with their geometry')
    D=d+1; N=k*D-1
    factor=F(k)*comb(2*N,N)/(a*4**N)
    QL=factor*Q**(2*k)
    threshold=F(k)**D*Q**2/(4*a*a*D)**D
    improvement=factor**D*Q
    need(threshold==rational(example['threshold_ratio']) and threshold>=1,
         'sufficient square-amplification threshold failed')
    need(improvement==rational(example['improvement_ratio']) and improvement>1,
         'exact spectral amplification failed')
    need(2*N==example['final_dimension'] and QL==rational(example['final_Q']),
         'square recipe has wrong final invariant')
    need(QL**D>Q**(2*N+1),'cross-powered root comparison failed')
    return dict(kind=kind,seed_dimension=d,seed_Q=str(Q),joins=k,dimension=2*N,
                final_Q=str(QL),threshold_ratio=str(threshold),
                improvement_ratio=str(improvement),strict_spectral_improvement=True)



def mutation_tests(cases):
    targets=[]
    c=deepcopy(cases[0]); c['expected']['A']=str(F(c['expected']['A'])+1)
    targets.append(('wrong expectation',c))
    c=deepcopy(cases[0]); c['points'][0][0]=str(F(c['points'][0][0])+1)
    targets.append(('nonzero mean',c))
    c=deepcopy(cases[0]); c['weights'][0]='-1'
    targets.append(('negative probability',c))
    original=next(c for c in cases if c.get('interior_counterexample'))
    c=deepcopy(original); d=c['dimension']
    c['symmetric_boundary_slabs']=[[str(int(i==j)) for j in range(d)] for i in range(d)]
    targets.append(('false boundary hypothesis',c))
    original=next(c for c in cases if c.get('expect_singular_all'))
    c=deepcopy(original); c['expected']['singular_defect']='0'
    targets.append(('discarded singular contribution',c))
    c=deepcopy(original); c['strictness_witness']['bound']=str(F(c['strictness_witness']['bound'])+1)
    targets.append(('corrupted strictness witness',c))
    result=[]
    for name,case in targets:
        try: check_case(case)
        except (ValueError,KeyError,TypeError,IndexError) as error:
            result.append(dict(name=name,rejected=True,reason=str(error)))
        else: raise ValueError(f'mutation accepted: {name}')
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--self-test',action='store_true')
    parser.add_argument('--report',type=Path)
    args=parser.parse_args()
    data=json.loads(args.certificate.read_text())
    need(data.get('schema')=='005-v3-random-determinants-1','unknown schema')
    need(isinstance(data.get('cases'),list) and data['cases'],'no fixed laws')
    results=[check_case(c) for c in data['cases']]
    report=dict(status='PASS',arithmetic='integer and Fraction; no floats or solver',
                laws=results,balanced_sign_tests=rademacher_tests(),
                direct_octahedron_geometry=octahedron_geometry(),
                spectral_examples=[check_spectral(e) for e in data['spectral_examples']],
                mutation_tests=mutation_tests(data['cases']) if args.self_test else [],
                scope='Finite exact checks only; paper.md proves all general and limiting assertions.')
    if args.self_test:
        bad=deepcopy(data['spectral_examples'][0])
        bad['final_Q']=str(F(bad['final_Q'])+1)
        try: check_spectral(bad)
        except ValueError as error:
            report['mutation_tests'].append(dict(name='corrupted spectral invariant',
                                                  rejected=True,reason=str(error)))
        else: raise ValueError('corrupted spectral invariant accepted')
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f'PASS: {len(results)} rational laws, {sum(r["ordered_lifted_tuples"] for r in results)} ordered lifted tuples')
    print(f'PASS: {report["balanced_sign_tests"]} balanced sign tests; {len(report["spectral_examples"])} spectral examples')
    if args.self_test: print(f'PASS: all {len(report["mutation_tests"])} deliberate corruptions rejected')
    for r in results:
        print(f'  {r["name"]}: a={r["normalized_a"]}, defect={r["defect"]}, singular={r["singular_defect"]}')

if __name__=='__main__': main()
