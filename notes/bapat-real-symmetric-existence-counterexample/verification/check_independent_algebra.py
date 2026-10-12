#!/usr/bin/env python3
"""Exact small-case checks of the proposed proof's algebra, independently written.
This is NOT an explicit real counterexample and does NOT replace limit proofs.
Only Python standard library; no floating-point arithmetic in the assertions.
"""
import sys

# Fail closed: these verifiers require assertions to remain enabled.
if not __debug__:
    sys.stderr.write("ERROR: assertions are disabled. Run without -O/-OO and without PYTHONOPTIMIZE.\n")
    raise SystemExit(2)

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial, comb
from random import Random


def mul_linear(poly, row):
    out = defaultdict(int)
    for alpha, c in poly.items():
        for j, v in enumerate(row):
            if v:
                beta = list(alpha); beta[j] += 1
                out[tuple(beta)] += c*v
    return {a:c for a,c in out.items() if c}


def product(rows, r):
    out = {(0,)*r: 1}
    for row in rows:
        out = mul_linear(out,row)
    return out


def mul(p,q):
    out = defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():
            out[tuple(x+y for x,y in zip(a,b))] += c*d
    return {a:c for a,c in out.items() if c}


def power(p,L,r):
    out={(0,)*r:1}
    for _ in range(L): out=mul(out,p)
    return out


def fischer(p):
    out=0
    for a,c in p.items():
        weight=1
        for k in a: weight *= factorial(k)
        out += weight*c*c
    return out


def wedge_polys(rows):
    n,r=len(rows),len(rows[0])
    ans={ab:defaultdict(int) for ab in combinations(range(r),2)}
    for i,j in combinations(range(n),2):
        comp=product([rows[k] for k in range(n) if k!=i and k!=j],r)
        for a,b in ans:
            d=rows[i][a]*rows[j][b]-rows[i][b]*rows[j][a]
            for alpha,c in comp.items(): ans[a,b][alpha] += d*c
    return {ab:{a:c for a,c in p.items() if c} for ab,p in ans.items()}


def direct(rows):
    n=len(rows)
    A=[[sum(x*y for x,y in zip(v,w)) for w in rows] for v in rows]
    per=der=0
    for p in permutations(range(n)):
        w=1
        for i in range(n): w*=A[i][p[i]]
        inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        per += w; der += inv*w
    return per,der

rng=Random(202610081235)
checks=0
for r in (1,2,3,4,5):
    for n in range(2,8):
        for k in range(3):
            rows=[tuple(rng.randint(-2,2) for _ in range(r)) for _ in range(n)]
            F=product(rows,r); S=wedge_polys(rows)
            per,der=direct(rows)
            assert per==fischer(F)
            assert 2*der==comb(n,2)*fischer(F)-sum(fischer(p) for p in S.values())
            checks+=1
print(f'PASS: {checks} exact arbitrary-rank endpoint/Fischer checks (r=1..5, n=2..7).')

checks=0
for r in (2,3,4):
    for n,L in ((2,2),(3,2),(3,3),(4,2)):
        rows=[tuple(rng.randint(-2,2) for _ in range(r)) for _ in range(n)]
        F=product(rows,r); S=wedge_polys(rows)
        repeated=[v for v in rows for _ in range(L)]
        assert product(repeated,r)==power(F,L,r)
        expected={ab:{a:L*L*c for a,c in mul(power(F,L-1,r),p).items()} for ab,p in S.items()}
        assert wedge_polys(repeated)==expected
        N=n*L
        factor=Fraction(factorial(N+r-3),factorial(N+r-1))
        assert factor==Fraction(1,(N+r-1)*(N+r-2))
        checks+=1
print(f'PASS: {checks} exact contiguous repetition and CP factorial quotient checks.')

checks=0
for t in (Fraction(1,2),Fraction(5,9),Fraction(3,5),Fraction(2,3),Fraction(7,10),Fraction(149,200)):
    c=(2*t-1)/(t*(3-4*t))
    assert c>=0
    assert 1-2*t+c*(3*t-4*t*t)==0
    assert 1-2*0+c*(3*0-4*0)>0
    assert 1-2*1+c*(3*1-4*1)<0
    checks+=1
print(f'PASS: {checks} exact peak-selector stationary point checks including t=1/2.')
print('These checks do not supply a finite numerical real counterexample or a dimension bound.')
