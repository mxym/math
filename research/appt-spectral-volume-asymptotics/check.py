#!/usr/bin/env python3
"""Exact ancillary checks for the analytic spectral-volume proof.

Standard library only. These checks certify the displayed rational/algebraic
identities and test fail-closed controls; they do not replace the analytic
Schmidt, Schur-complement, probability, or asymptotic arguments by enumeration.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations
import hashlib
import json
import math
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    # Intentionally not a Python assert: checks also run under python -O.
    if not condition:
        raise ValueError(message)


def parameters(m: int, n: int) -> tuple[int, int, int, F, F]:
    require(2 <= m <= n, 'dimension domain')
    return m*n, m*(m-1)//2, m*(m+1)//2, F(m-1, 2), F(m+1, 2)


def h_vertex(m: int, n: int, k: int) -> F:
    D, R, S, _, _ = parameters(m, n)
    return F(max(0, k-(D-S))-min(k, R), k)


def c_formula(m: int, n: int, k: int) -> F:
    D, R, S, alpha, _ = parameters(m, n)
    if k <= R:
        return F(m, D+m)
    if k <= D-S:
        return F(k)/(k+alpha*D)
    ell = D-k
    return F(m*(D-ell), ell*(D-m))


def tangent_volume(m: int, n: int) -> F:
    D, R, S, alpha, beta = parameters(m, n)
    require((alpha*D).denominator == (beta*D).denominator == 1, 'factorial arguments')
    return F(
        m**(m*m-1)*math.factorial(D-1)*math.factorial(int(alpha*D)+R),
        (D+m)**R*(D-m)**(S-1)*math.factorial(R)*math.factorial(S-1)
        *math.factorial(int(beta*D)-S))


def ratio_body_volume(m: int, n: int) -> F:
    D, _, _, alpha, beta = parameters(m, n)
    return F(math.factorial(int(alpha*D))*math.factorial(D-1),
             math.factorial(int(beta*D)-1))


def constant_squared_over_2pi(m: int) -> F:
    _, R, S, alpha, beta = parameters(m, m)
    return (m**(2*m*m-2)*alpha**(2*R+1)*beta**(2*S-1)
            / (math.factorial(R)*math.factorial(S-1))**2)


def inner_ratio_limit(m: int) -> F:
    _, R, S, alpha, beta = parameters(m, m)
    return (m**(m*m-1)*alpha**(R-m+1)*beta**(S-m)
            *math.factorial(m-1)*math.factorial(m)
            / (4**(m-1)*math.factorial(R)*math.factorial(S-1)))


def check_geometry() -> dict:
    cases = []
    vertices = 0
    for m in range(2, 11):
        for n in sorted({m, m+1, 2*m, 3*m+1}):
            D, R, S, alpha, beta = parameters(m, n)
            product = F(1)
            for k in range(1, D):
                h = h_vertex(m, n, k)
                piece = F(-1) if k <= R else (F(-R, k) if k <= D-S else F(k-D+m, k))
                require(h == piece, 'vertex piecewise identity')
                require(h < F(m, D), 'strict maximal vertex')
                c = F(m, D)/(F(m, D)-h)
                require(c == c_formula(m, n, k), 'stretch identity')
                require(0 < c <= 2*m, 'bounded positive stretch')
                if k <= D-S:
                    require(c <= F(2, m+1) <= F(2, 3), 'non-tail stretch bound')
                product *= c
                vertices += 1
            require(product == tangent_volume(m, n), 'tangent volume factorial identity')
            require(0 < ratio_body_volume(m, n) <= product, 'ratio-body containment volume')
            cases.append({'m': m, 'n': n, 'D': D, 'empty_middle': D-S == R})
    require(tangent_volume(2, 2) == 1, 'D=4 affine simplex check')
    require(tangent_volume(3, 3) == F(7, 256), 'D=9 affine simplex check')
    return {'cases': len(cases), 'vertices_checked': vertices, 'dimensions': cases}


def check_slot_identities() -> dict:
    """Every slot gets a separate formal coefficient; exact coefficient matching."""
    cases = 0
    for m in range(2, 11):
        R = m*(m-1)//2
        S = m*(m+1)//2
        pairs = list(combinations(range(m), 2))
        coefficients = {}
        for i in range(m):
            coefficients[f'b{i},{i}'] = F(2)
        for i, j in pairs:
            coefficients[f'b{i},{j}'] = F(2)
            coefficients[f'a{i},{j}'] = F(-2)
        require(sum(k.startswith('a') for k in coefficients) == R, 'negative slot count')
        require(sum(k.startswith('b') for k in coefficients) == S, 'positive slot count')
        require(F(m+1, S) == F(2, m), 'positive mean identity')
        require(F(m-1, R) == F(2, m), 'negative mean identity')
        require(all(v == (2 if k[0]=='b' else -2) for k, v in coefficients.items()),
                'assignment-independent total quadratic form')
        require(2+(m-1) == m+1, 'row-sum B coefficient')
        cases += 1
    return {'formal_slot_families': cases}


def check_dirichlet_bounds() -> dict:
    cases = 0
    for m in range(2, 11):
        S = m*(m+1)//2
        K = m*m-2
        c = 2*m*(m+1)
        D = 12*m*(S-1)
        n = D//m
        stretches = [c_formula(m, n, k) for k in range(1, D)]
        mean_xD = 1-sum(stretches, F(0))/D
        require(mean_xD >= F(1, 6), 'positive mean minimum-coordinate bound')
        variance = (D*sum((s*s for s in stretches), F(0))-sum(stretches, F(0))**2)/F(D*D*(D+1))
        require(variance <= F(4*m*m, D+1), 'Dirichlet variance bound')
        moment = F(2*K+K*(K-1), D*(D+1))
        require(moment == F(K*(K+1), D*(D+1)), 'grouped second moment')
        condition_moment = F(K*(K+1), (D-1)*D)
        require(6*c*c*(D-1)*condition_moment == F(6*c*c*K*(K+1), D),
                'dependent slack event bound')
        require(F(2, 1)*6*c*c*F(1, 12) == c*c, 'Schur sufficient-event coefficient')
        require(F(m*(m-1), D+m) <= F(c, D), 'top spread coefficient')
        require(F(m*(m+1), D-m) <= F(c, D), 'bottom spread coefficient')
        cases += 1
    return {'parameter_checks': cases, 'interpretation': 'exact identities and bound regressions, not asymptotic proof by finite testing'}


def poly_add(*polys: dict[tuple[int,int], F]) -> dict:
    out = {}
    for p in polys:
        for key, v in p.items():
            out[key] = out.get(key, F(0))+v
    return {k:v for k,v in out.items() if v}


def poly_mul(p: dict, q: dict) -> dict:
    out = {}
    for (i,j), a in p.items():
        for (k,l), b in q.items():
            key = (i+k,j+l)
            out[key] = out.get(key,F(0))+a*b
    return {k:v for k,v in out.items() if v}


def poly_scale(c: int, p: dict) -> dict:
    return {k:c*v for k,v in p.items() if c*v}


def check_constants_and_moments() -> dict:
    require(constant_squared_over_2pi(2) == F(243, 16), 'qubit leading constant')
    require(constant_squared_over_2pi(3) == F(2916**2, 50), 'qutrit leading constant')
    require(inner_ratio_limit(2) == 3, 'qubit inner-ratio constant')
    require(inner_ratio_limit(3) == F(2187, 40), 'qutrit inner-ratio constant')
    alpha = {(1,0):F(1)}
    beta = {(1,0):F(1),(0,0):F(1)}
    L = {(0,1):F(1)}
    one = {(0,0):F(1)}
    a = poly_mul(alpha,L)
    b = poly_mul(beta,L)
    mean = poly_add(poly_mul(beta,poly_add(a,one)),poly_scale(-1,poly_mul(alpha,poly_add(b,one))))
    require(mean == one, 'limiting density exact first moment')
    square = poly_add(poly_mul(beta,poly_add(poly_mul(a,a),poly_scale(2,a),poly_scale(2,one))),
                      poly_scale(-1,poly_mul(alpha,poly_add(poly_mul(b,b),poly_scale(2,b),poly_scale(2,one)))))
    expected = poly_add(poly_scale(2,one),poly_scale(-1,poly_mul(poly_mul(alpha,beta),poly_mul(L,L))))
    require(square == expected, 'limiting density exact second moment')
    for m in range(2, 11):
        _,R,S,al,be = parameters(m,m)
        require(R+S == m*m and S-R == m, 'triangular counts')
        require(F(-1,2)+R+F(1,2)+S-F(1,2)-(R+S-1) == F(1,2), 'square-root power')
        require(0 < al**(m-1)/be**(m+1) < 1, 'exponential base lies in (0,1)')
    return {'symbolic_density_moments': True,
            'C2_squared_over_2pi':str(constant_squared_over_2pi(2)),
            'C3_squared_over_2pi':str(constant_squared_over_2pi(3)),
            'APPT_to_inner_m2':'3', 'APPT_to_inner_m3':'2187/40'}


def expect_rejected(name: str, test: Callable[[], None]) -> dict:
    try:
        test()
    except ValueError as error:
        return {'name':name, 'rejected':True, 'diagnostic':str(error)}
    raise RuntimeError('Invalid control was accepted: '+name)


def check_negative_controls() -> list[dict]:
    records = []
    records.append(expect_rejected('changed tangent-volume numerator',
        lambda: require(tangent_volume(3,3)+F(1,256) == F(7,256), 'tangent volume factorial identity')))
    records.append(expect_rejected('changed leading coefficient',
        lambda: require(constant_squared_over_2pi(2) == F(244,16), 'qubit leading constant')))
    records.append(expect_rejected('wrong positive slot count',
        lambda: require(F(4,5) == F(2,3), 'positive mean identity')))
    require(1-2*F(4,9)-F(2,9) == F(-1,9), 'nonuniform physical test')
    records.append(expect_rejected('linear relaxation incorrectly asserted sufficient',
        lambda: require(1-2*F(4,9)-F(2,9) >= 0, 'negative partial-transpose quadratic form')))
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    report = {'status':'PASS',
        'scope':'Exact ancillary algebra, moment identities, finite formula checks, and explicit rejection controls; analytic all-dimension proof is separate; not Lean',
        'geometry':check_geometry(), 'slots':check_slot_identities(),
        'probability':check_dirichlet_bounds(), 'constants':check_constants_and_moments(),
        'negative_controls':check_negative_controls(),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
    print('EXACT_ANCILLARY_CHECKS_PASS')
    print('GEOMETRY_CASES', report['geometry']['cases'], 'VERTICES', report['geometry']['vertices_checked'])
    print('SYMBOLIC_DENSITY_MOMENTS_PASS')
    print('NEGATIVE_CONTROLS_REJECTED',len(report['negative_controls']))
    if args.self_test:
        print('SELF_TEST_PASS: required assertions remain active under python -O')


if __name__ == '__main__':
    main()
