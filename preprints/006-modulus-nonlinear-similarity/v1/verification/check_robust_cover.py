#!/usr/bin/env python3
"""Exact checker for a FINITE rational robust normalized-cover certificate.

A certificate specifies positive rational points, nonnegative error radii,
periodically repeated OPEN intervals, and a density budget. It asserts that for
all x in [0,1], t in [1,2], and independent errors of the specified sizes,
at least one x+t*a+error lies in the holes. This is not a computed witness for
the manuscript's arbitrarily-small-density theorem. Worst-case exponential.
All decisions use Fraction arithmetic; closed boundary failures are retained.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

Point = tuple[Q, Q]
Interval = tuple[Q, Q]


def q(value: object) -> Q:
    if isinstance(value, bool) or not isinstance(value, (int, str)):
        raise ValueError('Use integer or string rationals, never floating-point values')
    return Q(value)


def floor(x: Q) -> int:
    return x.numerator // x.denominator


def ceil(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def translates(holes: list[Interval], lo: Q, hi: Q) -> list[Interval]:
    raw = []
    for a, b in holes:
        if a >= b:
            raise ValueError('Each open interval must have a < b')
        for m in range(ceil(lo-b), floor(hi-a)+1):
            raw.append((a+m, b+m))
    raw.sort()
    result: list[Interval] = []
    for a, b in raw:
        # Strict inequality: touching open intervals leave a singleton gap.
        if result and a < result[-1][1]:
            result[-1] = (result[-1][0], max(b, result[-1][1]))
        else:
            result.append((a, b))
    return result


def complement(holes: list[Interval], lo: Q, hi: Q) -> list[Interval]:
    merged = translates(holes, lo, hi)
    if not merged:
        return [(lo, hi)]
    raw = [(lo, merged[0][0])]
    raw += [(merged[i][1], merged[i+1][0]) for i in range(len(merged)-1)]
    raw.append((merged[-1][1], hi))
    result = []
    for a, b in raw:
        a, b = max(a, lo), min(b, hi)
        if a <= b:
            result.append((a, b))
    return result


def density(holes: list[Interval]) -> Q:
    return sum((max(Q(0), min(Q(1), b)-max(Q(0), a))
                for a, b in translates(holes, Q(0), Q(1))), Q(0))


def contains(z: Q, holes: list[Interval]) -> bool:
    return any(floor(z-b)+1 <= ceil(z-a)-1 for a, b in holes)


def clip(poly: tuple[Point, ...], a: Q, b: Q, c: Q) -> tuple[Point, ...]:
    """Intersect a closed convex polygon/segment/point with a*x+b*t <= c."""
    if not poly:
        return ()
    result = []
    prev = poly[-1]
    vp = a*prev[0]+b*prev[1]-c
    for current in poly:
        vc = a*current[0]+b*current[1]-c
        if (vp <= 0) != (vc <= 0):
            s = vp/(vp-vc)
            result.append((prev[0]+s*(current[0]-prev[0]),
                           prev[1]+s*(current[1]-prev[1])))
        if vc <= 0:
            result.append(current)
        prev, vp = current, vc
    return tuple(dict.fromkeys(result))


def check(data: dict) -> dict:
    points = [q(a) for a in data['points']]
    radii = [q(a) for a in data.get('radii', ['0']*len(points))]
    if not points or len(points) != len(radii):
        raise ValueError('Nonempty points and one radius per point are required')
    if any(a <= 0 for a in points) or any(r < 0 for r in radii):
        raise ValueError('Points must be positive; radii must be nonnegative')
    holes = [(q(row[0]), q(row[1])) for row in data['holes']]
    budget = q(data.get('max_density', '1'))
    if not 0 <= budget <= 1:
        raise ValueError('Density budget must lie in [0,1]')
    rho = density(holes)
    if rho > budget:
        return {'valid': False, 'reason': 'density budget exceeded', 'density': str(rho)}
    lo = min(a-r for a, r in zip(points, radii))
    hi = max(1+2*a+r for a, r in zip(points, radii))
    gaps = complement(holes, lo, hi)
    rect = ((Q(0), Q(1)), (Q(1), Q(1)), (Q(1), Q(2)), (Q(0), Q(2)))
    stack = [(0, rect, ())]
    states = 0
    while stack:
        j, poly, selected = stack.pop()
        states += 1
        if j == len(points):
            x, t = poly[0]
            errors = []
            for a, r, (l, u) in zip(points, radii, selected):
                z = x+t*a
                e = min(max(z, l), u)-z
                if abs(e) > r or contains(z+e, holes):
                    raise ArithmeticError('Independently checked witness is invalid')
                errors.append(str(e))
            return {'valid': False, 'reason': 'robust uncovered parameter pair',
                    'density': str(rho), 'states_visited': states,
                    'witness': {'x': str(x), 't': str(t), 'errors': errors}}
        a, r = points[j], radii[j]
        for l, u in gaps:
            reduced = clip(poly, Q(1), a, u+r)
            reduced = clip(reduced, Q(-1), -a, -l+r)
            if reduced:
                stack.append((j+1, reduced, selected+((l, u),)))
    return {'valid': True, 'density': str(rho), 'states_visited': states,
            'claim': 'all normalized parameters and all listed bounded independent errors are covered'}


def self_test() -> dict:
    basic = {'points': ['1/8', '1/4'], 'holes': [['1/10', '1']], 'max_density': '9/10'}
    cases = [
        ('ordinary toy cover', basic, True),
        ('robust toy cover radius 1/100', {**basic, 'radii': ['1/100']*2}, True),
        ('sharp boundary failure at radius 1/80', {**basic, 'radii': ['1/80']*2}, False),
        ('larger uncertainty fails', {**basic, 'radii': ['1/50']*2}, False),
        ('boundary-only ordinary failure', {'points': ['1/8', '1/4'], 'holes': [['1/8', '1']]}, False),
        ('singleton gaps retained', {'points': ['1/8', '3/8'], 'holes': [['0', '1/2'], ['1/2', '1']]}, False),
        ('whole circle robust cover', {'points': ['1/8'], 'radii': ['2'], 'holes': [['-1/10', '11/10']]}, True),
        ('empty holes', {'points': ['1/8'], 'holes': []}, False),
        ('density budget enforced', {**basic, 'max_density': '1/2'}, False),
    ]
    results = []
    for name, data, expected in cases:
        answer = check(data)
        if answer['valid'] != expected:
            raise ArithmeticError(f'Regression failed: {name}: {answer}')
        results.append({'name': name, **answer})
    return {'status': 'PASS', 'arithmetic': 'exact rational', 'tests': results,
            'scope': 'finite regression checks only; not a global small-density witness or formalization'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path, nargs='?')
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.self_test:
        result = self_test()
    elif args.certificate:
        result = check(json.loads(args.certificate.read_text(encoding='utf-8')))
    else:
        parser.error('Provide a certificate or --self-test')
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')
    if result.get('valid') is False:
        sys.exit(1)


if __name__ == '__main__':
    main()
