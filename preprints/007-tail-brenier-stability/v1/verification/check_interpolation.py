#!/usr/bin/env python3
"""Exact finite checks for the tail-sensitive interpolation manuscript.

Checks rational piecewise-affine convex functions and piecewise-constant
probability densities on [0,1], including densities that are not log-concave.
Also checks exact sharpness-ramp identities and exponent/homogeneity identities.
These are regression tests, not a formalization of the general theorem or of
manuscript 001's source-dependent optimal-transport input.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import random


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def stats(knots: list[Q], us: list[Q], vs: list[Q], weights: list[Q],
          u0: Q, v0: Q, threshold: Q) -> tuple[Q, Q, Q, Q]:
    """Return (gradient distance squared, centered potential variance, tail, V)."""
    count = len(knots)-1
    require(len(us) == len(vs) == len(weights) == count, 'Partition lengths')
    require(knots[0] == 0 and knots[-1] == 1, 'Domain endpoints')
    require(all(knots[i] < knots[i+1] for i in range(count)), 'Ordered knots')
    require(us == sorted(us) and vs == sorted(vs), 'Convex slopes')
    require(all(w >= 0 for w in weights), 'Nonnegative density')
    lengths = [knots[i+1]-knots[i] for i in range(count)]
    mass = sum((w*l for w, l in zip(weights, lengths)), Q(0))
    require(mass > 0, 'Positive density mass')
    density = [w/mass for w in weights]
    variation = (density[0]+density[-1]
                 +sum(abs(density[i+1]-density[i]) for i in range(count-1)))/2
    f = u0-v0
    mean = square = grad = tail = Q(0)
    for l, a, b, w in zip(lengths, us, vs, density):
        s = a-b
        mean += w*(f*l+s*l*l/2)
        square += w*(f*f*l+f*s*l*l+s*s*l**3/3)
        grad += w*s*s*l
        tail += w*l*((a*a if abs(a) > threshold else 0)
                      +(b*b if abs(b) > threshold else 0))
        f += s*l
    delta2 = square-mean*mean
    require(delta2 >= 0, 'Nonnegative exact variance')
    return grad, delta2, tail, variation


def verify(seed: int = 604007, cases: int = 240) -> dict:
    rng = random.Random(seed)
    checks = 0
    min_margin = None
    min_case = None
    for case in range(cases):
        count = rng.randint(2, 9)
        internal = sorted(rng.sample(range(1, 24), count-1))
        knots = [Q(0)]+[Q(t, 24) for t in internal]+[Q(1)]
        us = sorted(Q(rng.randint(-24, 24), rng.randint(1, 5)) for _ in range(count))
        vs = sorted(Q(rng.randint(-24, 24), rng.randint(1, 5)) for _ in range(count))
        # Zero-density gaps and non-unimodal profiles intentionally included.
        weights = [Q(rng.randint(0, 5)) for _ in range(count)]
        if not any(weights):
            weights[0] = Q(1)
        u0, v0 = Q(rng.randint(-3, 3)), Q(rng.randint(-3, 3))
        for L in (Q(1, 8), Q(1, 2), Q(2), Q(7), Q(32)):
            X2, delta2, tail, V = stats(knots, us, vs, weights, u0, v0, L)
            for h in (Q(1, 100), Q(1, 8), Q(1, 2), Q(1), Q(3)):
                rhs = 12*delta2/h**2+28*V*L**2*h+4*tail
                margin = rhs-X2
                require(margin >= 0, f'Interpolation case={case}, L={L}, h={h}')
                checks += 1
                if min_margin is None or margin < min_margin:
                    min_margin, min_case = margin, [case, str(L), str(h)]
    ramps = []
    for p in (2, 3, 4, 6, 10):
        for denominator in (2, 3, 5):
            t = Q(1, denominator)
            a = t**p
            height = 1/t
            X2, delta2, tail, V = stats([Q(0), 1-a, Q(1)], [Q(0), height],
                                      [Q(0), Q(0)], [Q(1), Q(1)], Q(0), Q(0), height/2)
            moment = a*height**p
            require(moment == 1, 'Ramp pth moment')
            require(X2 == t**(p-2), 'Ramp gradient norm')
            require(delta2 == t**(3*p-2)*(Q(1, 3)-a/4), 'Ramp centered potential variance')
            ramps.append({'p': p, 't': str(t), 'moment': str(moment),
                          'X_squared': str(X2), 'delta_squared': str(delta2)})
    exponents = []
    for p in (Q(5, 2), Q(3), Q(4), Q(6), Q(10), Q(100)):
        alpha = (p-2)/(3*p-2)
        beta = 2*p/(3*p-2)
        require(alpha+beta == 1, 'Target-dilation homogeneity')
        require((Q(1, 2)-1/p)/(Q(3, 2)-1/p) == alpha, 'Sharp ramp exponent')
        require(Q(1, 3)*(p-2)/(p-Q(2, 3)) == alpha, 'Balancing exponent')
        require(0 < alpha < Q(1, 3), 'Exponent range')
        exponents.append({'p': str(p), 'map_upper_exponent': str(alpha),
                          'moment_radius_exponent': str(beta)})
    # For the robust cover toy used by manuscript 006, the largest admissible
    # closed uncertainty is NOT accepted at equality; that is checked there.
    return {'status': 'PASS', 'arithmetic': 'exact integers and Fraction',
            'seed': seed, 'piecewise_affine_instances': cases,
            'inequality_checks': checks, 'minimum_margin': str(min_margin),
            'minimum_margin_case': min_case, 'sharp_ramp_checks': ramps,
            'exponent_identities': exponents,
            'scope': 'finite exact regression; not a proof-assistant formalization, '
                     'not a check of 001, and not sharpness for the Wasserstein map exponent'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', type=int, default=240)
    parser.add_argument('--output', type=Path, default=Path('verification/exact_checks.json'))
    args = parser.parse_args()
    if not 1 <= args.cases <= 10000:
        parser.error('--cases must lie in 1..10000')
    result = verify(cases=args.cases)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(f"PASS: {result['inequality_checks']} exact piecewise-affine inequality checks")
    print(f"PASS: {len(result['sharp_ramp_checks'])} sharp-ramp identities and {len(result['exponent_identities'])} exponent cases")
    print('Scope: regression only; transport applications retain the explicit potential-stability input.')


if __name__ == '__main__':
    main()
