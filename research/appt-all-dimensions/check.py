#!/usr/bin/env python3
"""Auxiliary exact checks, not a Lean proof or a finite replacement for PROOF.md.

All symbolic arithmetic uses Fraction coefficients and polynomial expansion.
No optimizer, floating point, computer-algebra package, or external network is used.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parent
NAMES = ('D', 'k', 'c', 'l', 'r', 'x', 'y', 'm', 'n', 'u', 'H')
N = len(NAMES)
ZERO = (0,) * N


class CertificateMismatch(ValueError):
    pass


class Poly:
    """Sparse commutative polynomials over Q; zero coefficients are removed."""
    def __init__(self, terms=None):
        self.terms = {tuple(k): F(v) for k, v in (terms or {}).items() if v}

    @staticmethod
    def constant(value):
        return Poly({ZERO: F(value)})

    @staticmethod
    def variable(name):
        exponents = [0] * N
        exponents[NAMES.index(name)] = 1
        return Poly({tuple(exponents): F(1)})

    def __add__(self, other):
        if not isinstance(other, Poly):
            other = Poly.constant(other)
        terms = dict(self.terms)
        for k, v in other.terms.items():
            terms[k] = terms.get(k, F(0)) + v
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Poly) else -F(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if not isinstance(other, Poly):
            other = Poly.constant(other)
        terms = {}
        for k, a in self.terms.items():
            for l, b in other.terms.items():
                exponent = tuple(x + y for x, y in zip(k, l))
                terms[exponent] = terms.get(exponent, F(0)) + a * b
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError('Expected a nonnegative integer exponent')
        out = Poly.constant(1)
        for _ in range(exponent):
            out = out * self
        return out

    def derivative(self, name):
        j = NAMES.index(name)
        terms = {}
        for exps, coefficient in self.terms.items():
            if exps[j]:
                new = list(exps)
                new[j] -= 1
                terms[tuple(new)] = coefficient * exps[j]
        return Poly(terms)

    def substitute(self, name, replacement):
        j = NAMES.index(name)
        out = Poly()
        for exps, coefficient in self.terms.items():
            other = list(exps)
            other[j] = 0
            out += Poly({tuple(other): coefficient}) * replacement ** exps[j]
        return out


def require(condition, message):
    if not condition:
        raise CertificateMismatch(message)


def identity(name, left: Poly, right: Poly, checks):
    require((left - right).terms == {}, 'Polynomial identity mismatch: ' + name)
    checks.append(name)


def rational_identity(name, left_num, left_den, right_num, right_den, checks):
    require(left_den.terms and right_den.terms, 'Zero formal denominator: ' + name)
    identity(name, left_num * right_den, right_num * left_den, checks)


def verify(data, run_regressions=True):
    require(data.get('format') == 'appt-two-level-exact-algebra-v1', 'Unknown certificate format')
    checks = []
    v = {name: Poly.variable(name) for name in NAMES}
    D, k, c, l, r, x, y, m, n, u, H = [v[name] for name in NAMES]
    one = Poly.constant(1)

    plus_num, plus_den = D + 2*k*c + k*c**2, D + k*c
    minus_num, minus_den = D - 2*l*c + l*c**2, D - l*c
    identity('two-level positive contrast: centered moment',
             D*plus_num - plus_den**2, k*(D-k)*c**2, checks)
    identity('two-level negative contrast: centered moment',
             D*minus_num - minus_den**2, l*(D-l)*c**2, checks)
    identity('positive contrast derivative numerator',
             plus_num.derivative('c')*plus_den - 2*plus_num*plus_den.derivative('c'),
             2*k*(D-k)*c, checks)
    identity('negative contrast derivative numerator',
             minus_num.derivative('c')*minus_den - 2*minus_num*minus_den.derivative('c'),
             2*l*(D-l)*c, checks)

    f_num, f_den = D*(m-1)**2+4*m*k, D*(m-1)+2*k
    identity('middle-rank derivative numerator',
             f_num.derivative('k')*f_den-2*f_num*f_den.derivative('k'),
             4*(D*(m-1)-2*m*k), checks)
    identity('ceiling strictly beats floor at a half-integer optimum',
             m*(H+2)*(H-1)**2-m*(H-2)*(H+1)**2, 4*m, checks)
    identity('clique padding inequality',
             (r-1)**2-F(1,2)*r*(r+1)+1, F(1,2)*(r-1)*(r-4), checks)
    identity('few-high-eigenvalues comparison with rank-one spike',
             4*(D-1)*(D+2*u)**2-4*(D-u**2)*(D+2)**2,
             4*D*(u-1)*(D*u+5*D+8*u+4), checks)

    hnum, hden = l*(D-l), r*D-2*l
    identity('lower tail-rank subinterval monotonicity numerator',
             hnum.derivative('l')*hden-2*hnum*hden.derivative('l'),
             D*(r*D-2*(r-1)*l), checks)
    B = 2*D**2+(r**2-8*r-12)*D+8*r**2+8*r-8
    identity('tail bound below spike: cleared denominators',
             4*(D-1)*(D-r)**2-(2*D-r**2)*(D+2)**2, D*B, checks)
    require(data.get('shifted_tail_variables') == ['x', 'y'], 'Wrong sign-certificate variables')
    sign_poly = Poly()
    for term in data['shifted_tail_polynomial']:
        powers, coefficient = term['powers'], term['coefficient']
        require(len(powers) == 2 and all(isinstance(e, int) and e >= 0 for e in powers),
                'Invalid sign-certificate exponent')
        require(isinstance(coefficient, int) and coefficient > 0,
                'Nonpositive sign-certificate coefficient')
        sign_poly += coefficient * x**powers[0] * y**powers[1]
    require(sign_poly.terms.get(ZERO, 0) > 0, 'No strictly positive constant')
    identity('shifted tail positivity certificate (equation 17)',
             B.substitute('D', r**2+x).substitute('r', 3+y), sign_poly, checks)

    identity('l=1 comparison', (D+8)*(D-1)-(D+2)**2, 3*(D-4), checks)
    identity('l=2 comparison for D>=12', (D+8)*(D-2)-(D+2)**2, 2*(D-10), checks)
    identity('l=3 comparison',
             3*(D+8)*(D-2)**2-(3*D-8)*(D+2)**2, 8*(D-4)**2, checks)
    # delta=2/(l+1), with all denominators cleared before comparison.
    tail_num = D*(l+1)**2-4*l*(l+1)+4*l
    tail_den = D*(l+1)-2*l
    identity('polytope high-rank vertices lie in the separable ball',
             tail_den**2-(D-1)*tail_num, D*(l-1)**2, checks)
    # Here r is the independent total contrast s and q is encoded by c.
    multinum, multiden = D+2*r+c, D+r
    identity('flat-minimum multi-level monotonicity numerator',
             multinum.derivative('r')*multiden-2*multinum*multiden.derivative('r'),
             -2*(r+c), checks)
    identity('relaxation spectrum purity gap',
             (D+11)*(D+2)**2-(D+8)*(D+3)**2, D**2-9*D-28, checks)

    special = data['exceptional_D9_l2']
    delta = F(*special['delta'])
    purity = F(9-4*delta+2*delta*delta, (9-2*delta)**2)
    require(purity == F(*special['purity']) == F(127,968), 'Wrong exceptional purity')
    require(F(17,121)-purity == F(*special['gap_to_spike']) == F(9,968), 'Wrong exceptional gap')
    require(delta*F(6,5) == 1, 'Invalid exceptional Schmidt constraint')
    checks.append('D=9, l=2 exact exceptional calculation')
    ex = data['uniform_schmidt_relaxation_counterexample']
    nums = ex['numerator_spectrum']
    require(ex['D'] == 16 and nums == [3,2]+[1]*14, 'Wrong relaxation witness')
    p = F(sum(a*a for a in nums), sum(nums)**2)
    require(p == F(*ex['purity']) == F(27,361), 'Wrong relaxation purity')
    require(p-F(2,27) == F(*ex['gap_over_conjectured']) == F(7,9747), 'Wrong relaxation gap')
    require((1-2*F(4,9)-F(2,9))/sum(nums) == F(*ex['negative_quadratic_form']),
            'Wrong negative quantum expectation')
    checks.append('exact non-APPT relaxation witness arithmetic')

    phase_quadruples = 0
    for q in range(1,9):
        for i,j,k0,l0 in itertools.product(range(q), repeat=4):
            powers = [0]*q
            for index,sign in [(i,1),(j,-1),(k0,-1),(l0,1)]:
                powers[index] += sign
            survives = all(a % 3 == 0 for a in powers)
            expected = (i == j and k0 == l0) or (i == k0 and j == l0)
            require(survives == expected, 'Phase-average character mismatch')
            phase_quadruples += 1
    checks.append('phase-character finite regressions, ranks 1 through 8')

    counts = {'symbolic_identities_and_exact_controls': len(checks),
              'phase_quadruples': phase_quadruples, 'dimension_pairs': 0,
              'middle_integer_ranks': 0, 'graph_rank_regressions': 0,
              'tail_rank_regressions': 0}
    if run_regressions:
        for mm in range(3,25):
            R, S = mm*(mm-1)//2, mm*(mm+1)//2
            for kk in range(1,R):
                if kk <= 2:
                    radius_sq = F(kk)
                elif kk <= 4:
                    radius_sq = F(4)
                elif kk == 5:
                    radius_sq = F(25,4)
                else:
                    qq=2
                    while (qq+1)*qq//2 <= kk:
                        qq += 1
                    require(4 <= qq < mm, 'Wrong graph padding support')
                    radius_sq = F((qq-1)**2)
                require(radius_sq >= kk, 'Graph lower bound failed')
                counts['graph_rank_regressions'] += 1
            for nn in range(mm,2*mm+13):
                DD=mm*nn
                tt=((mm-1)*nn+1)//2
                require(R <= tt <= DD-S, 'Candidate rank outside middle interval')
                pp = lambda kk: F(DD*(mm-1)**2+4*mm*kk, (DD*(mm-1)+2*kk)**2)
                for kk in range(R,DD-S+1):
                    require(pp(kk) <= pp(tt), 'Incorrect middle integer maximizer')
                    require(kk == tt or pp(kk) < pp(tt), 'Unexpected integer tie')
                    counts['middle_integer_ranks'] += 1
                for ll in range(1,S):
                    rr=1
                    while rr*(rr+1)//2 < ll:
                        rr += 1
                    if rr >= 3:
                        bound=F(1,DD)+F(2*DD-rr*rr,DD*(DD-rr)**2)
                        require(bound < F(DD+8,(DD+2)**2), 'Tail comparison failed')
                    counts['tail_rank_regressions'] += 1
                counts['dimension_pairs'] += 1
    return {'checks': checks, 'counts': counts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=ROOT/'CERTIFICATES.json')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    data = json.loads(args.certificate.read_text())
    try:
        outcome = verify(data)
        bad = copy.deepcopy(data)
        for term in bad['shifted_tail_polynomial']:
            if term['powers'] == [0,0]:
                term['coefficient'] += 1
        try:
            verify(bad, run_regressions=False)
        except CertificateMismatch as error:
            require(str(error) == 'Polynomial identity mismatch: shifted tail positivity certificate (equation 17)',
                    'Wrong rejection cause: '+str(error))
            rejection = str(error)
        else:
            raise CertificateMismatch('A mutated constant was accepted')
        report = {'status': 'PASS',
                  'scope': 'Auxiliary exact algebra and finite regressions; not a Lean proof of the quantum theorems or the full conjecture',
                  'certificate_sha256': hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
                  'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  **outcome, 'negative_control': {'constant_changed_from': 7, 'to': 8,
                                               'expected_rejection': rejection},
                  'seconds': round(time.monotonic()-start,3)}
        text = json.dumps(report, indent=2)+'\n'
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(text)
        print(text, end='')
        return 0
    except (CertificateMismatch, KeyError, TypeError, ValueError) as error:
        print('EXACT_CHECK_FAILED: '+str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
