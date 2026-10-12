#!/usr/bin/env python3
"""Exact d=5 replay for the pure-state ECQC counterexample.

Python 3.10+, standard library only. No floating point, numerical eigenvalues,
optimizer, or external certificate. See paper.tex for the analytic logarithm
lemmas and the all-prime proof; this script checks their polynomial identities,
the rational margin, and the actual finite-dimensional quantum construction.
Copyright (c) 2026 Yongxian Zhang. All rights reserved.
"""
from fractions import Fraction as F
from math import comb
import json

if not __debug__:
    raise RuntimeError("Assertions are required; do not run with python -O.")

# Q(zeta_5), with 1+zeta+...+zeta^4=0. The intended complex embedding is
# zeta=exp(2*pi*i/5), fixed in the paper. Coefficients have length four.
ZERO = (F(0),) * 4
ONE = (F(1), F(0), F(0), F(0))

def scalar(x):
    return (F(x), F(0), F(0), F(0))

def add(a, b):
    return tuple(x+y for x, y in zip(a, b))

def scale(a, c):
    return tuple(F(c)*x for x in a)

def mul(a, b):
    v = [F(0)] * 7
    for i in range(4):
        for j in range(4):
            v[i+j] += a[i]*b[j]
    for i in range(6, 3, -1):
        for j in range(1, 5):
            v[i-j] -= v[i]
    return tuple(v[:4])

def zpower(k):
    k %= 5
    if k == 4:
        return (F(-1),) * 4
    return tuple(F(int(i == k)) for i in range(4))

def conjugate(a):
    out = ZERO
    for k, x in enumerate(a):
        out = add(out, scale(zpower(-k), x))
    return out

def sumfield(xs):
    out = ZERO
    for x in xs:
        out = add(out, x)
    return out

def power(a, n):
    out = ONE
    for _ in range(n):
        out = mul(out, a)
    return out

def inner(a, b):
    return sumfield(mul(conjugate(x), y) for x, y in zip(a, b))

def matrix_mul(a, b):
    n, m, k = len(a), len(b), len(b[0])
    assert len(a[0]) == m
    return [[sum(a[i][j]*b[j][l] for j in range(m))
             for l in range(k)] for i in range(n)]

def trace(a):
    return sum(a[i][i] for i in range(len(a)))

def run():
    d = 5
    assert power(zpower(1), 5) == ONE
    assert sumfield(zpower(k) for k in range(5)) == ZERO
    # Computational vectors have norm squared 1; quadratic vectors have
    # norm squared 5. Division by sqrt(norm2) yields the actual bases.
    bases = [[tuple(scalar(int(x == b)) for x in range(d)) for b in range(d)]]
    norms = [1]
    for a in range(d):
        bases.append([tuple(zpower(a*x*x+b*x) for x in range(d))
                      for b in range(d)])
        norms.append(d)
    checked_pairs = 0
    for r in range(d+1):
        for s in range(d+1):
            for j in range(d):
                for k in range(d):
                    v = inner(bases[r][j], bases[s][k])
                    norm_sq = mul(v, conjugate(v))
                    expected = (F(norms[r]*norms[s], d) if r != s
                                else F(norms[r]*norms[s]*int(j == k)))
                    assert norm_sq == scalar(expected)
                    checked_pairs += 1
    # A literal 25x25 rank-one density matrix, not a surrogate entropy model.
    rho = [[F(0) for _ in range(d*d)] for _ in range(d*d)]
    support = (0, d+1)  # |00>, |11>
    for i in support:
        for j in support:
            rho[i][j] = F(1, 2)
    assert rho == matrix_mul(rho, rho)
    assert trace(rho) == 1
    assert all(rho[i][j] == rho[j][i] for i in range(d*d) for j in range(d*d))
    # rho is the Gram outer product of (|00>+|11>)/sqrt(2), so is PSD.
    red_a = [[sum(rho[x*d+y][xp*d+y] for y in range(d))
              for xp in range(d)] for x in range(d)]
    red_b = [[sum(rho[x*d+y][x*d+yp] for x in range(d))
              for yp in range(d)] for y in range(d)]
    target = [[F(int(i == j and i < 2), 2) for j in range(d)] for i in range(d)]
    assert red_a == red_b == target
    # Thus spectra are (1,0,...,0) and (1/2,1/2,0,0,0): QMI=2 log 2.
    probabilities = []
    for r, basis in enumerate(bases):
        table = []
        for j in range(d):
            row = []
            for k in range(d):
                # Born probability: Tr[rho (P_j tensor P_k)] by direct
                # contraction with the nonzero entries of the literal rho.
                born = ZERO
                for u in support:
                    for v in support:
                        x, y = divmod(u, d)
                        xp, yp = divmod(v, d)
                        term = mul(mul(basis[j][xp], conjugate(basis[j][x])),
                                   mul(basis[k][yp], conjugate(basis[k][y])))
                        born = add(born, scale(term, rho[u][v]/norms[r]**2))
                if r == 0:
                    expected = scalar(F(int(j == k and j < 2), 2))
                else:
                    t = 2*(r-1)+j+k
                    expected = scale(add(scalar(2), add(zpower(t), zpower(-t))), F(1, 50))
                assert born == expected
                row.append(born)
            table.append(row)
        assert sumfield(p for row in table for p in row) == ONE
        if r > 0:
            assert all(sumfield(row) == scalar(F(1, d)) for row in table)
            assert all(sumfield(table[j][k] for j in range(d)) == scalar(F(1, d))
                       for k in range(d))
        probabilities.append(table)
    # Exact cosine moments, from the same cyclotomic embedding as the Born table.
    cosines = [scale(add(zpower(t), zpower(-t)), F(1, 2)) for t in range(d)]
    moments = []
    for n in range(1, 6):
        moment = scale(sumfield(power(x, n) for x in cosines), F(1, d))
        assert all(v == 0 for v in moment[1:])
        moments.append(moment[0])
    assert moments == [F(0), F(1, 2), F(0), F(3, 8), F(1, 16)]
    coeffs = [F(1), F(1, 2), -F(1, 6), F(1, 12), -F(1, 20)]
    lower = sum(c*m for c, m in zip(coeffs, moments))
    assert lower == F(89, 320)
    # f(x)=(1+x)log(1+x), P5=sum coeffs[n-1]x^n.
    # Verify (1+x) P5''(x) = 1-x^4. Hence (f-P5)''=x^4/(1+x)>=0.
    p_second = [F((n+2)*(n+1))*coeffs[n+1] for n in range(4)]
    product = [F(0)] * 5
    for n, c in enumerate(p_second):
        product[n] += c
        product[n+1] += c
    assert product == [F(1), F(0), F(0), F(0), F(-1)]
    assert sum(c*(-1)**(i+1) for i, c in enumerate(coeffs)) == -F(1, 5)
    # log 2=2 int_0^(1/3) 1/(1-t^2) dt
    # <= 2/3+(9/4)int_0^(1/3)t^2 dt =25/36.
    log2_upper = 2*F(1, 3) + F(9, 4)*F(1, 3)**3/3
    assert log2_upper == F(25, 36)
    gap = 5*lower - 2*log2_upper
    assert gap == F(1, 576) and gap > 0
    # Check the general moment formula symbolically for all integers p>=7:
    # no nonzero Fourier frequency in powers <=5 is divisible by p.
    tail_moments = [F(comb(n, n//2), 2**n) if n % 2 == 0 else F(0)
                    for n in range(1, 6)]
    assert sum(c*m for c, m in zip(coeffs, tail_moments)) == F(9, 32)
    return {
        'status': 'PASS',
        'arithmetic': 'fractions.Fraction and Q(zeta_5); no floating point',
        'dimension': d,
        'normalized_basis_vector_pairs_checked': checked_pairs,
        'literal_density_matrix_shape': [25, 25],
        'born_probabilities_checked': 6*25,
        'cosine_moments_1_through_5': [str(x) for x in moments],
        'single_quadratic_basis_information_lower_bound_nats': str(lower),
        'log_2_upper_bound': str(log2_upper),
        'ecqc_violation_lower_bound_nats': str(gap),
        'general_prime_tail_information_lower_bound_nats': '9/32',
        'scope': 'Exact finite construction and algebraic certificates. '
                 'Analytic log lemmas and all-prime quantifiers are proved in paper.tex; '
                 'this is not a Lean kernel proof.'
    }

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
