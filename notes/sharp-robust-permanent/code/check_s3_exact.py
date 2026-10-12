#!/usr/bin/env python3
"""Exact symbolic replay of the sharp 3x3 permanent/determinant certificate.

Requires SymPy (tested with version 1.14). Everything is computed exactly
in Q(sqrt(3))[a,b,c]; no floating-point calculations are used.
The analytic inequality follows from the printed PSD principal minors.
"""
from itertools import permutations
from math import factorial
from sympy import (Matrix, Rational, eye, expand, simplify, sqrt,
                   symbols, prod, zeros)


def even_permutation(pi):
    return sum(pi[i] > pi[j] for i in range(3)
               for j in range(i+1, 3)) % 2 == 0


def assert_zero(expr, context):
    if isinstance(expr, Matrix):
        assert all(simplify(x) == 0 for x in expr), context
    else:
        assert simplify(expand(expr)) == 0, context


a, b, c = symbols('a b c', real=True)
s = sqrt(3)
beta = 2 / s
lam = beta - 1
k = 2*s - 3
h = s - 1
M = Matrix([[0, (2-beta)*c, beta*b],
            [beta*c, 0, (2-beta)*a],
            [(2-beta)*b, beta*a, 0]])
H = Matrix([[a*a + k*b*b, -h*a*b, -h*a*c],
            [-h*a*b, b*b+k*c*c, -h*b*c],
            [-h*a*c, -h*b*c, c*c+k*a*a]])
assert_zero(H - Rational(3,4) * (beta**2 * (a*a+b*b+c*c) * eye(3)
                                - M.T * M), 'PSD gram identity')
print('PASS exact Gram/PSD identity for arbitrary real a,b,c')

minor12 = k * (a*a*b*b+a*a*c*c+b**4+k*b*b*c*c)
assert_zero(H.extract([0,1],[0,1]).det()-minor12, 'minor12')
cyc = [{a:b,b:c,c:a}, {a:c,b:a,c:b}]
for indices, replacements in zip(([1,2], [0,2]), cyc):
    assert_zero(H.extract(indices,indices).det()
                - minor12.subs(replacements, simultaneous=True),
                f'principal minor {indices}')
print('PASS all three exact nonnegative principal 2x2 minor factorizations')

X, Y, Z = a*a, b*b, c*c
delta = (X+Y+Z)*(X*Y+Y*Z+Z*X)-9*X*Y*Z
assert_zero(H.det() - k*k * delta, 'det factor')
assert_zero(delta - (a**4*b*b+a**4*c*c+
                     b**4*a*a+b**4*c*c+
                     c**4*a*a+c**4*b*b-6*a*a*b*b*c*c),
            'symmetric polynomial identity')
print('PASS exact determinant factorization; AM-GM proves nonnegativity')

perms = list(permutations(range(3)))
evens = [pi for pi in perms if even_permutation(pi)]
odds = [pi for pi in perms if not even_permutation(pi)]
assert len(evens)==len(odds)==3
for ev in evens:
    for od in odds:
        assert sum(ev[i] == od[i] for i in range(3)) == 1
assert_zero(lam - (2*s/3 - 1), 'lambda simplification')
assert_zero(Rational(1,2)*lam - (1/s - Rational(1,2)), 'radius')
assert_zero(beta / 6 - 1/(3*s), 'norm constant')
assert k.is_positive and h.is_positive
print('PASS all S3 parity intersections and exact robustness threshold')
print('CERTIFICATE REPLAY PASSED')
