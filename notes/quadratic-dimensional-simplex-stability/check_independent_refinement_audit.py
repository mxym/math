#!/usr/bin/env python3
"""Independent finite regression for the analytic audit. No producer imports.
Exact law/witness and actual-body determinant checks; floating log checks of gates.
Finite tests do not prove the universal theorem.
"""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
from collections import Counter
from math import factorial, prod, sqrt, log, exp, log1p


def det(rows):
    a = [list(map(F, r)) for r in rows]
    v = F(1)
    for j in range(len(a)):
        k = next((k for k in range(j, len(a)) if a[k][j]), None)
        if k is None: return F(0)
        if k != j:
            a[j], a[k] = a[k], a[j]
            v = -v
        z = a[j][j]
        v *= z
        for k in range(j + 1, len(a)):
            q = a[k][j] / z
            for l in range(j + 1, len(a)):
                a[k][l] -= q * a[j][l]
    return v


def lifted(points): return det([tuple(x) + (F(1),) for x in points])
def pos(x): return max(F(0), x)
def norm(x): return max(map(abs, x))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))


def psi(base, y, z):
    fy, fz = lifted(base + [y]), lifted(base + [z])
    return min(pos(fy), pos(-fz)) + min(pos(-fy), pos(fz))


def witness(W, x):
    n = len(W)
    g = sum(psi([W[k] for k in range(n) if k != i], W[i], x)
            for i in range(n))
    g += sum(psi([x] + [W[k] for k in range(n) if k not in (i,j)], W[i], W[j])
             for i,j in combinations(range(n), 2))
    return g


def law_check(name, law):
    pts = list(law)
    d = len(pts[0]); n = d + 1; N = F(n*(n+1), 2)
    assert sum(law.values()) == 1
    assert all(sum(p*x[k] for x,p in law.items()) == 0 for k in range(d))
    diameter = max(norm(sub(x,y)) for x in pts for y in pts)
    A = factorial(d)*sum(prod(law[x] for x in xs)*abs(det(xs))
                         for xs in combinations(pts,d))
    B = factorial(n)*sum(prod(law[x] for x in xs)*abs(lifted(xs))
                         for xs in combinations(pts,n))
    D = B-A
    assert A > 0 and B > 0 and D >= 0
    EH = EHpos = EHsing = weighted_mass = weighted_ratio = F(0)
    best = None; nonsingular = 0
    for inds in combinations_with_replacement(range(len(pts)), n):
        multiplicity = factorial(n)
        for c in Counter(inds).values(): multiplicity //= factorial(c)
        probability = multiplicity*prod(law[pts[i]] for i in inds)
        W = [pts[i] for i in inds]
        signed = lifted(W); V = abs(signed)
        G = {x:witness(W,x) for x in pts}
        H = sum(law[x]*G[x] for x in pts)
        EH += probability*H
        if not V:
            EHsing += probability*H
            continue
        nonsingular += 1
        EHpos += probability*H
        weighted_mass += probability*V/B
        weighted_ratio += probability*V/B*(H/V)
        h = F(0)
        for x in pts:
            alpha = []
            for i in range(n):
                W1 = list(W); W1[i] = x
                alpha.append(lifted(W1)/signed)
            assert sum(alpha) == 1
            r = max(range(n), key=lambda i: alpha[i])
            negative = sum(pos(-a) for a in alpha)
            other_positive = sum(pos(a) for i,a in enumerate(alpha) if i != r)
            phi = sum(min(F(1),pos(-a)) for a in alpha)
            phi += sum(min(pos(alpha[i]),pos(alpha[j])) for i,j in combinations(range(n),2))
            extra = sum(min(pos(-alpha[i]),pos(-alpha[j])) for i,j in combinations(range(n),2))
            assert G[x] == V*(phi+extra)
            assert min(F(1),negative+other_positive) <= phi
            assert norm(sub(x,W[r])) <= diameter*phi
            h += law[x]*norm(sub(x,W[r]))
        assert h <= diameter*H/V
        candidate = (H/V,h)
        if best is None or candidate < best: best = candidate
    assert EH == EHpos+EHsing and EH <= N*D
    assert weighted_mass == 1 and weighted_ratio == EHpos/B
    assert best[0] <= N*D/B and best[1] <= diameter*N*D/B
    print(f'{name}: PASS; d={d}; nonsingular unordered anchors={nonsingular}; D/B={D/B}; singular E[H]={EHsing}')


def simplex_law(d,t,center=F(0)):
    out = {}
    for j in range(d):
        out[tuple(F(int(i==j)) for i in range(d))] = (1-center)*t/(1+d*t)
    out[tuple(-t for _ in range(d))] = (1-center)/(1+d*t)
    if center: out[(F(0),)*d] = center
    return out


law_check('one-dimensional asymmetric law', {(F(-100),):F(1,102),(F(0),):F(1,102),(F(1),):F(100,102)})
law_check('two-dimensional exact equality', simplex_law(2,F(1,1000)))
law_check('two-dimensional nearly flat cross', {(F(0),F(0)):F(1,5),(F(1),F(0)):F(1,5),(F(-1),F(0)):F(1,5),(F(0),F(1,1000)):F(1,5),(F(0),F(-1,1000)):F(1,5)})
law_check('three-dimensional rare atoms plus origin', simplex_law(3,F(1,1000),F(1,10)))
law_check('four-dimensional simplex plus origin', simplex_law(4,F(1,7),F(1,20)))

# Direct facet determinant certificate for square-based iterated pyramids.
for d in range(3,13):
    u = [[F(-1 if i<2 else -2) if i==j else F(0) for j in range(d)] for i in range(d)]
    u += [[F(j==0 or j>=2) for j in range(d)], [F(j==1 or j>=2) for j in range(d)]]
    b = [F(0)]*d+[F(1),F(1)]
    H = sum(abs(det([u[i] for i in ids])) for ids in combinations(range(d+2),d))
    L = sum(abs(det([u[i]+[b[i]] for i in ids])) for ids in combinations(range(d+2),d+1))
    assert H == d*2**(d-1) and L == 2**d
    assert L/(2*H) == F(1,d)
    # e_3,...,e_d must all be present, so enumerate only four base triangles.
    square = [(F(0),F(0)),(F(1),F(0)),(F(0),F(1)),(F(1),F(1))]
    assert all(abs(lifted(xs)) == 1 for xs in combinations(square,3))
print('Square-pyramid direct facet certificate: PASS, dimensions 3 through 12.')

# Independent log-domain constants, avoiding overflows and underflowed e0.
max_ratio = (0,0)
for d in range(3,10001):
    m=d-1; R=d*sqrt(d+2); M=4*d*R; C=(d+1)**2*(d+2); L=2*sqrt(m)*(R+1)
    # log(1+M+d*2**(d-1)*M) by stable log-sum-exp.
    terms=[0,log(M),log(d)+(d-1)*log(2)+log(M)]
    mx=max(terms); lb=mx+log(sum(exp(x-mx) for x in terms))
    lJ=log(d/2)+d*log(2*R)+lb
    lG=log(8)+log(R+1)+log(d)+log(L)+(lJ+log(C))/m
    le0=-(lJ+log(C))-m*log(8*d*L)
    assert abs(lG+le0/m-log(R+1)) < 1e-10
    assert lJ >= log(M) and sqrt(m)/(8*d*L) <= .5
    assert lG < 20*log(2)+6*log(d)
    ratio=exp(lG-6*log(d))
    if ratio>max_ratio[1]: max_ratio=(d,ratio)
print(f'Constants and gate: PASS, dimensions 3 through 10000; largest tested G/d^6={max_ratio[1]:.12g} at d={max_ratio[0]}.')
print('ALL INDEPENDENT REGRESSIONS PASSED. Finite tests supplement the analytic audit.')
