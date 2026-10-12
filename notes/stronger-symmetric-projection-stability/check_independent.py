#!/usr/bin/env python3
"""Independent exact checks of edge cases, not certificates of universal lemmas."""
from fractions import Fraction as F
from itertools import product
from math import factorial
from random import Random
import json


def require(c, msg):
    if not c:
        raise RuntimeError(msg)


def det(cols):
    n = len(cols)
    m = [[F(cols[j][i]) for j in range(n)] for i in range(n)]
    out = F(1)
    for j in range(n):
        k = next((i for i in range(j, n) if m[i][j]), None)
        if k is None:
            return F(0)
        if k != j:
            m[k], m[j] = m[j], m[k]
            out = -out
        pivot = m[j][j]
        out *= pivot
        for i in range(j+1, n):
            z = m[i][j]/pivot
            for k in range(j+1, n):
                m[i][k] -= z*m[j][k]
    return out


def fourth(cols):
    return sorted((abs(det(cols[:i]+cols[i+1:]))
                   for i in range(len(cols))), reverse=True)[3]


def apply(u, a):
    return tuple(sum(u[j][i]*a[j] for j in range(len(a)))
                 for i in range(len(a)))


def truncate(a):
    order = sorted(range(len(a)), key=lambda i: (-abs(a[i]), i))
    return tuple(a[i] if i in order[:2] else F(0) for i in range(len(a))), abs(a[order[2]])


def run():
    rng = Random(751996)
    ill = 0
    smallest = F(1)
    for d in range(3, 7):
        axes = [tuple(F(i == j) for i in range(d)) for j in range(d)]
        for denom in (2, 17, 10**3, 10**9):
            u = [axes[0]] + [tuple((axes[0][i]+F(1,denom)*axes[j][i]) /
                                   (1+F(1,denom)) for i in range(d))
                                  for j in range(1,d)]
            D = abs(det(u))
            require(D == F(1,denom+1)**(d-1), 'ill-conditioned determinant')
            smallest = min(smallest, D)
            for _ in range(8):
                a = tuple(F(rng.randrange(-8,9),8)/D for _ in range(d))
                b = tuple(F(rng.randrange(-8,9),8)/D for _ in range(d))
                at, sa = truncate(a)
                bt, sb = truncate(b)
                j = rng.randrange(d)
                basis = u[:j]+u[j+1:]
                original = fourth(basis+[apply(u,a),apply(u,b)])
                formula = sorted([D*abs(a[j]),D*abs(b[j])] +
                                  [D*abs(a[i]*b[j]-a[j]*b[i])
                                   for i in range(d) if i != j], reverse=True)[3]
                perturbed = fourth(basis+[apply(u,at),apply(u,bt)])
                require(original == formula, 'oblique cofactor formula')
                require(abs(original-perturbed) <= 2*(sa+sb), 'oblique truncation')
                ill += 1

    # Independent piecewise-linear convex negative-quadrant frontiers.
    # x starts at -b, g starts at zero, and slopes increase, including zero,
    # exactly one, very large slopes, and crossings at either endpoint.
    planar = 0
    for _ in range(1000):
        n = rng.randrange(1,15)
        widths = [F(rng.randrange(1,100),rng.randrange(1,100)) for _ in range(n)]
        slopes = sorted(rng.choice([F(0),F(1),F(10**9),F(1,10**9),
                                   F(rng.randrange(1,100),rng.randrange(1,100))])
                        for _ in range(n))
        x, g = -sum(widths), F(0)
        values = [g-x]
        integral = F(0)
        for width, slope in zip(widths,slopes):
            integral += width*min(F(1),slope)
            x, g = x+width, g+width*slope
            values.append(g-x)
        require(x == 0, 'planar endpoint')
        require(integral == min(values), 'planar mixed-normal identity')
        planar += 1

    # A genuine scope guard: an even polar-boundary law with zero scalar
    # defect can have positive fourth cofactor. It is not a cone law.
    z = [(F(1),F(0),F(0)),(F(0),F(1),F(0)),(F(0),F(0),F(1)),
         (F(1,3),)*3]
    A = sum(abs(det([z[i] for i in inds])) for inds in product(range(4),repeat=3))/F(4**3)
    phi, B = F(0), F(0)
    for inds in product(range(4),repeat=4):
        cols = [z[i] for i in inds]
        phi += fourth(cols)/F(4**4)
        for signs in product((-1,1),repeat=4):
            lifts = [tuple(signs[j]*x for x in cols[j])+(F(1),) for j in range(4)]
            B += abs(det(lifts))/F(4**4*16)
    require((A,B,phi)==(F(3,16),F(3,8),F(1,32)), 'non-cone scope guard')
    require(F(1,2)-B/(4*A)==0, 'scope guard zero deficit')

    # Exact dimension inequalities used in both coefficient simplifications.
    require(20**2 * 2**15 < 4096**2, 'd12 prefactor')
    require(5**2 * 2**11 < 243**2, 'd19 prefactor')
    require(19*3 >=57 and 39*3>=115, 'worst dimension')
    return {'status':'PASS','oblique_ill_conditioned_sections':ill,
            'minimum_basis_determinant':str(smallest),
            'planar_convex_frontiers':planar,
            'noncone_scope_guard':{'A':str(A),'B':str(B),'fourth':str(phi),'deficit':'0'},
            'constant_prefactors':'exact checks; monotone dimension steps proved analytically',
            'scope':'Finite exact stress checks only; not a proof of all-body coarea or nonatomic statements.'}


if __name__ == '__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
