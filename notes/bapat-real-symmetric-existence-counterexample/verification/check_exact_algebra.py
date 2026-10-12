#!/usr/bin/env python3
"""Independent exact-integer checks; evidence for identities, not the asymptotic proof."""
import sys

# Fail closed: these verifiers require assertions to remain enabled.
if not __debug__:
    sys.stderr.write("ERROR: assertions are disabled. Run without -O/-OO and without PYTHONOPTIMIZE.\n")
    raise SystemExit(2)

from collections import defaultdict
from itertools import combinations, permutations
from math import factorial, prod, comb
from fractions import Fraction
import random


def clean(p):
    return {a:c for a,c in p.items() if c}


def mul(p,q):
    out=defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():
            out[tuple(x+y for x,y in zip(a,b))]+=c*d
    return clean(out)


def scale(p,c):
    return clean({a:c*v for a,v in p.items()})


def power(p,k,r):
    out={(0,)*r:1}
    for _ in range(k): out=mul(out,p)
    return out


def forms(rows):
    n,r=len(rows),len(rows[0]); lin=[]
    for row in rows:
        p={}
        for a,x in enumerate(row):
            e=[0]*r;e[a]=1
            if x: p[tuple(e)]=x
        lin.append(p)
    F={(0,)*r:1}
    for p in lin:F=mul(F,p)
    S={ab:defaultdict(int) for ab in combinations(range(r),2)}
    for i,j in combinations(range(n),2):
        P={(0,)*r:1}
        for k in range(n):
            if k not in (i,j):P=mul(P,lin[k])
        for a,b in S:
            det=rows[i][a]*rows[j][b]-rows[i][b]*rows[j][a]
            for e,c in P.items():S[a,b][e]+=det*c
    return F,{ab:clean(p) for ab,p in S.items()}


def norm(p):
    return sum(c*c*prod(factorial(k) for k in a) for a,c in p.items())


def eval_poly(p,z):
    return sum(c*prod(x**k for x,k in zip(z,a)) for a,c in p.items())


def perm_and_deriv(rows):
    n=len(rows)
    A=[[sum(x*y for x,y in zip(u,v)) for v in rows] for u in rows]
    per=deriv=0
    for s in permutations(range(n)):
        x=prod(A[i][s[i]] for i in range(n))
        inv=sum(s[i]>s[j] for i,j in combinations(range(n),2))
        per+=x;deriv+=inv*x
    return per,deriv


def run():
    rng=random.Random(20261008)
    cases=[]
    for r in (2,3,4,5):
        for n in range(2,7):
            for case in range(4):
                rows=[[rng.randint(-3,3) for _ in range(r)] for _ in range(n)]
                F,S=forms(rows); per,d=perm_and_deriv(rows)
                assert norm(F)==per
                assert 2*d==comb(n,2)*norm(F)-sum(norm(s) for s in S.values())
                cases.append((n,r,case))
    print(f'PASS: {len(cases)} exact integer Gram/Fischer/marked-inversion tests (r=2..5,n=2..6).')
    rep=0
    for r in (2,3,4):
        for n,L in ((2,2),(3,2),(2,3)):
            rows=[[rng.randint(-2,2) for _ in range(r)] for _ in range(n)]
            F,S=forms(rows); FL,SL=forms([row for row in rows for _ in range(L)])
            assert FL==power(F,L,r)
            for ab in S:assert SL[ab]==scale(mul(power(F,L-1,r),S[ab]),L*L)
            rep+=1
    print(f'PASS: {rep} exact polynomial contiguous-repetition tests.')
    # CP^(r-1) monomial normalization and the degree-two factorial quotient.
    for r in range(2,7):
        for N in range(2,15):
            cF=Fraction(factorial(N+r-1),factorial(r-1))
            cS=Fraction(factorial(N+r-3),factorial(r-1))
            assert cS/cF==Fraction(1,(N+r-1)*(N+r-2))
    print('PASS: CP factorial quotient for r=2..6,N=2..14.')
    # Selector critical equation at rational t. No numerical root computation.
    for t in (Fraction(1,2),Fraction(3,5),Fraction(2,3),Fraction(7,10),Fraction(749,1000)):
        c=(2*t-1)/(t*(3-4*t))
        assert c>=0 and 1-2*t+c*(3*t-4*t*t)==0
        assert 1-2*Fraction(0)+c*(0)==1
        assert 1-2*Fraction(1)+c*(3-4)<0
    print('PASS: exact selector critical equation at five rational t values.')

if __name__=='__main__':run()
