#!/usr/bin/env python3
"""Exact finite algebra checks for the smooth steep-layer counterexample.

These checks verify the first recursion parameters, identities controlling a
single layer, and two-atom coupling/map costs. They do not numerically integrate
the infinite smooth density, certify its limiting tails, or formalize the proof.
The second recursion exponent is kept symbolically; enormous powers are never
materialized. Standard-library integers and Fraction only.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def ceil(x: Q) -> int:
    return -((-x.numerator)//x.denominator)


def verify() -> dict:
    B2, D2 = Q(2), Q(2)
    N2 = 4*(1+ceil(B2+D2))
    require(N2 == 20, 'First layer exponent')
    a2 = Q(1, 2**N2)
    M2, eps2 = a2**-2, a2**4
    B3 = Q(9, 2)+M2*(1-eps2/2)
    D3 = 3+M2
    N3 = 9*(1+ceil(B3+D3))
    require(N3 >= 9*(1+B3+D3), 'Next exponent lower bound')
    require(N3 > 10**12, 'Expected scale growth')
    # Keep a3=2^(-N3) as text: the proof is exact without printing its digits.
    layers = {'n2': {'B': str(B2), 'D': str(D2), 'N': N2,
                     'a': str(a2), 'M': str(M2), 'epsilon': str(eps2)},
              'n3': {'B': str(B3), 'D': str(D3), 'N': N3,
                     'a_symbolic': f'2^(-{N3})', 'power_not_materialized': True}}
    parameter_checks = 0
    for n in range(2, 13):
        for B in (Q(0), Q(1, 3), Q(2), Q(17, 2), Q(128)):
            for D in (Q(1, 2), Q(2), Q(7), Q(64)):
                N = n*n*(1+ceil(B+D))
                a = Q(1, 2**N)
                require(N >= n*n*(1+B+D), 'Uniform exponent choice')
                require(D*a <= 1, 'Convex-tangent majorant coefficient')
                require(B/N <= Q(1, n*n), 'Subdominant log-density exponent')
                require(a**4/a+1/((a**-2)*a) == a**3+a, 'Normalized right-tail cost')
                require(a**3+a < 1, 'Uniform tail majorant')
                parameter_checks += 1
    cost_checks = 0
    examples = []
    for q in (2, 3, 4, 6):
        theta = Q(1, 2)-Q(1, q)
        alpha = theta/(1+theta)
        require(alpha == Q(q-2, 3*q-2), 'Sharp transport exponent')
        require(alpha-theta*(1-alpha) == 0, 'Critical log-quotient coefficient')
        for z in (Q(1, 2), Q(1, 3), Q(1, 5)):
            m, R = z**q, 1/z
            require(m*R**q == 1, 'Exactly normalized target moment')
            for t in (Q(1, 10), Q(1, 5), Q(1, 3)):
                v1, v2 = (1-t*t)/(1+t*t), 2*t/(1+t*t)
                delta2 = (1-v1)**2+v2**2
                require(v1*v1+v2*v2 == 1, 'Unit rare-atom direction')
                require(delta2 == 4*t*t/(1+t*t) < 2, 'Exact chord cost')
                optimal = m*R*R*delta2
                for i in range(17):
                    rare_match = m*Q(i, 16)
                    # Since m<=1/4, every listed rare-match mass is feasible.
                    require(1-2*m+rare_match >= 0, 'Coupling feasibility')
                    cost = R*R*(rare_match*delta2+2*(m-rare_match))
                    require(cost >= optimal, 'Two-atom optimal target coupling')
                    require((cost == optimal) == (i == 16), 'Strict coupling minimum')
                    cost_checks += 1
                for i in range(9):
                    intersection = m*Q(i, 8)
                    symdiff = 2*(m-intersection)
                    direct = R*R*(m-intersection)+R*R*(m-intersection)
                    direct += R*R*delta2*intersection
                    formula = R*R*(symdiff+delta2*intersection)
                    require(direct == formula, 'Exact common-source map cost')
                    cost_checks += 1
            examples.append({'q': q, 'm': str(m), 'R': str(R),
                             'moment': '1', 'critical_exponent': str(alpha)})
    return {'status': 'PASS', 'arithmetic': 'exact rational and integer',
            'first_two_recursion_stages': layers,
            'parameter_instances': parameter_checks,
            'two_atom_cost_checks': cost_checks,
            'normalized_examples': examples,
            'scope': 'finite algebra checks only; smoothness, tail limits, '
                     'and the single-source all-q theorem are proved in the manuscript'}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, default=Path('verification/steep_example_checks.json'))
    args = p.parse_args()
    result = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(f"PASS: {result['parameter_instances']} exact layer-parameter cases")
    print(f"PASS: {result['two_atom_cost_checks']} exact two-atom coupling/map identities")
    print('Scope: algebra regression, not numerical verification of an infinite density.')


if __name__ == '__main__':
    main()
