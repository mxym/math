#!/usr/bin/env python3
"""Exact formula/control checks and finite real-power diagnostics, not Lean.

The universal theorems are the written proofs. No unitary sampling is used.
Explicit exceptions and a real non-PPT state protect the physical boundary.
"""
from argparse import ArgumentParser
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def shift_poly(a, b):
    out = [0] * len(a)
    power = [1]
    for c in a:
        for i, x in enumerate(power):
            out[i] += c * x
        power = poly_mul(power, [b, 1])
    return out


def spectrum(d, kind, j):
    if kind == 'R':
        return [F(1, j)] * j + [F(0)] * (d - j)
    if kind == 'T':
        z = d - 1 + j
        return [F(2, z)] * j + [F(1, z)] * (d - 1 - j) + [F(0)]
    z = d + 2 * j
    return [F(3, z)] * j + [F(1, z)] * (d - j)


def purity(x):
    return sum(t * t for t in x)


def endpoint_checks():
    count = 0
    for d in range(8, 161):
        j = [d // 4, (d - 1) // 4, (d + 2) // 4, (d + 1) // 4][d % 4]
        q, mu = d + 2 * j, purity(spectrum(d, 'P', j))
        require(mu > F(9, 8 * (d - 1)), 'known T purity gap')
        require(mu >= F(1, d - 2), 'known uniform purity gap')
        for i in range(1, d - 2):
            t = spectrum(d, 'T', i)
            require(sum(t) == 1 and t[0] == sum(t[-3:]), 'outer T vertex')
            if i <= 2 * j + 1 and 3 * i >= 4 * j - d + 3:
                require(F(1, q) <= t[-2] <= t[0] <= F(3, q), 'secant support')
                require(mu > purity(t), 'secant strict mean')
            elif i > 2 * j + 1:
                require(t[0] < mu, 'Jensen support below mean')
            else:
                require(i == 1 and d % 4 in (2, 3), 'missed case list')
                p = spectrum(d, 'P', j - 1)
                require(p[-1] <= t[-2] <= t[0] <= p[0], 'exception support')
                require(purity(p) > purity(t), 'exception mean gap')
            count += 1
    require(shift_poly([32, -32, -32, 5], 8) == [288, 416, 88, 5], 'T polynomial')
    require(shift_poly([8, -4, -8, 1], 9) == [53, 95, 19, 1], 'R polynomial')
    require(shift_poly([-1, -4, -2, 6], 2) == [31, 60, 34, 6], 'D mod2 polynomial')
    require(shift_poly([-6, -12, 4, 16], 1) == [2, 44, 52, 16], 'D mod3 polynomial')
    require(purity(spectrum(8, 'R', 6)) == purity(spectrum(8, 'P', 2)) == F(1, 6),
            'retained outer equality exception')
    pole = F(43, 2048)
    t6 = [F(5, 324), F(35, 2401), F(25, 2048)]
    require(all(t < pole for t in t6), 'D6 base comparisons')
    require(4 * F(2, 3)**4 == F(64, 81) < 1, 'D6 rank4 bound')
    require(F(19, 14)**5 > 4 and 64 > F(232, 7), 'D4 near-cap base')
    require(64 * F(5, 19) - F(15, 7) > 0, 'D4 near-cap derivative')
    x = F(23, 32)
    require(1 + x + x*x/2 + x*x*x/6 == F(400871, 196608) > 2,
            'D4 far-region exponential certificate')
    return {'exact_endpoint_comparisons': count, 'polynomial_coefficient_identities': 4,
            'D8_alpha2_outer_tie': '1/6', 'D6_alpha4_pole': str(pole)}


def negative_control():
    rho = [[F(0) for _ in range(4)] for _ in range(4)]
    b = [0, 1, -1, 0]
    for i, j in product(range(4), repeat=2):
        rho[i][j] = F(b[i] * b[j], 4)
    rho[3][3] += F(1, 2)
    squared = [[sum(rho[i][k]*rho[k][j] for k in range(4))
                for j in range(4)] for i in range(4)]
    require(sum(rho[i][i] for i in range(4)) == 1, 'density trace')
    require(all(squared[i][j] == rho[i][j]/2 for i, j in product(range(4), repeat=2)),
            'two orthogonal rank-one positive summands with eigenvalue1/2')
    pt = [[F(0) for _ in range(4)] for _ in range(4)]
    for a, b0, c, d in product(range(2), repeat=4):
        pt[2*a+b0][2*c+d] = rho[2*a+d][2*c+b0]
    w = [2, 0, 0, 1]
    value = sum(w[i]*pt[i][j]*w[j] for i, j in product(range(4), repeat=2)) / 5
    require(value == F(-1, 10), 'actual negative PPT expectation')
    lam = [F(1, 2), F(1, 2), F(0), F(0)]
    require(lam[0] <= sum(lam[-3:]), 'bad state passes linear outer test')
    require((lam[0]-lam[-2])**2 > 4*lam[-1]*lam[-3], 'bad state fails determinant')
    return {'actual_partial_transpose_expectation': str(value),
            'outer_test_passes': True, 'physical_rank_two_test_fails': True}


def phase_checks():
    cases = 0
    roots = [(1, 0), (0, 1), (-1, -1)]  # exact a+b*zeta, zeta^2+zeta+1=0
    for m in range(1, 5):
        for i, j, k, ell in product(range(m), repeat=4):
            total = [0, 0]
            for t in product(range(3), repeat=m):
                a, b = roots[(t[i]-t[j]-t[k]+t[ell]) % 3]
                total[0] += a
                total[1] += b
            survives = (i == j and k == ell) or (i == k and j == ell)
            require(total == [3**m if survives else 0, 0], 'finite product phase identity')
            cases += 1
    examples = [(2, 3, [F(3,5), F(4,5)]),
                (3, 3, [F(1,3), F(2,3), F(2,3)]),
                (4, 5, [F(1,2)]*4)]
    for m, n, s in examples:
        require(sum(x*x for x in s) == 1, 'rational Schmidt norm')
        off = sum(s[i]*s[j] for i, j in product(range(m), repeat=2) if i != j)
        require(all(1-2*s[i]*s[j] >= 0 for i, j in product(range(m), repeat=2) if i != j),
                'nonnegative residual product weights')
        omega_trace = 1 + off
        residual_trace = m*n - 2*off
        require(2*omega_trace + residual_trace == m*n+2, 'normalization of product mixture')
    return {'exact_phase_matrix_entries': cases, 'rational_Schmidt_examples': len(examples),
            'scope': 'finite formula checks; the arbitrary-m identity is proved in writing'}


def dec(q):
    return Decimal(q.numerator) / Decimal(q.denominator)


def moment(s, a):
    counts = {}
    for x in s:
        if x:
            counts[x] = counts.get(x, 0) + 1
    return sum((n*(dec(x).ln()*a).exp() for x, n in counts.items()), Decimal(0))


def real_power_diagnostics():
    cases, rank_cases, records = 0, 0, []
    with localcontext() as ctx:
        ctx.prec = 80
        tol = Decimal('1e-65')
        for d in range(8, 45):
            for astr in ('2', '2.125', '2.5', '3', '4', '5', '8', '12', '24', '80'):
                a = Decimal(astr)
                p = [moment(spectrum(d, 'P', j), a) for j in range(1, d-2)]
                best = max(p)
                other = [moment(spectrum(d, 'R', r), a) for r in range(d-2, d+1)]
                other += [moment(spectrum(d, 'T', j), a) for j in range(1, d-2)]
                require(max(other) <= best*(1+tol), 'finite real-power envelope diagnosis')
                z = (Decimal(3).ln()*a).exp() - 1
                x = Decimal(d)*(z-2*a)/(2*(a-1)*z)
                lo = max(1, min(d-3, int(x)))
                hi = max(1, min(d-3, int(x)+1))
                require(max(p[lo-1], p[hi-1]) >= best*(1-tol), 'integer-rank diagnosis')
                cases += 1
                rank_cases += 1
        for d in (8, 10, 12, 20, 40, 80, 160):
            a = Decimal(d)/2+1
            p = [moment(spectrum(d, 'P', j), a) for j in range(1, d-2)]
            require(all(p[0] > val for val in p[1:]), 'finite sufficient-band strictness')
        for d in (40, 80, 160, 320):
            a = Decimal(d)/4
            ratio = moment(spectrum(d, 'P', 2), a)/moment(spectrum(d, 'P', 1), a)
            require(ratio > 1, 'actual qubit two-projection competition')
            records.append({'D': d, 'alpha': str(a), 'actual_qubit_rank2_to_pole_ratio': str(ratio)})
    return {'real_power_vertex_cases': cases, 'integer_rank_cases': rank_cases,
            'sufficient_band_dimensions': 7, 'actual_qubit_competitors': records,
            'precision_decimal_digits': 80, 'relative_tolerance': '1e-65',
            'scope': 'numerical evaluated formulas, not continuous optimization or sampled unitaries'}


def main():
    ap = ArgumentParser()
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    result = {'status': 'PASS', 'proof_kind': 'supporting exact and numerical diagnostics',
              'complete_lean': False, 'unitary_sampling': False,
              'endpoints': endpoint_checks(), 'negative_control': negative_control(),
              'phase_formula': phase_checks(), 'finite_real_powers': real_power_diagnostics()}
    payload = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.out:
        args.out.write_text(payload, encoding='utf-8')
    print(json.dumps({'status': 'PASS', 'endpoint_comparisons': result['endpoints']['exact_endpoint_comparisons'],
                      'phase_entries': result['phase_formula']['exact_phase_matrix_entries'],
                      'real_power_cases': result['finite_real_powers']['real_power_vertex_cases'],
                      'negative_control': result['negative_control']['actual_partial_transpose_expectation']}))


if __name__ == '__main__':
    main()
