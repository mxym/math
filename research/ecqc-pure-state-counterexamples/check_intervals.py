#!/usr/bin/env python3
"""Independent exact rational interval verification, including full Schmidt rank.

No imports from check_exact.py, floating point, or third-party libraries.
Logarithms use an atanh series with a proved geometric remainder; sqrt(5)
uses integer-square-root brackets. Decimal output is rounded outwards.
Copyright (c) 2026 Yongxian Zhang. All rights reserved.
"""
from fractions import Fraction as Q
from math import isqrt
import json

if not __debug__:
    raise RuntimeError("Assertions are required; do not run with python -O.")

DIGITS = 45
TERMS = 64
SCALE = 10**DIGITS
root_floor = isqrt(5*SCALE*SCALE)
SQRT5 = (Q(root_floor, SCALE), Q(root_floor+1, SCALE))
assert SQRT5[0]**2 < 5 < SQRT5[1]**2

def plus(x, y):
    return (x[0]+y[0], x[1]+y[1])

def neg(x):
    return (-x[1], -x[0])

def times(x, y):
    candidates = [a*b for a in x for b in y]
    return min(candidates), max(candidates)

def const(x):
    return Q(x), Q(x)

def scaled(x, q):
    return times(x, const(q))

def log_near_one(x):
    assert Q(1) <= x <= Q(2)
    z = (x-1)/(x+1)
    power = z
    partial = Q(0)
    for j in range(TERMS):
        partial += 2*power/(2*j+1)
        power *= z*z
    tail = 2*power/((2*TERMS+1)*(1-z*z))
    # z>=0; every omitted term is nonnegative.
    return partial, partial+tail

LOG2 = log_near_one(Q(2))

def log_rational(x):
    assert x > 0
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x >= 2:
        x /= 2
        k += 1
    return plus(log_near_one(x), scaled(LOG2, k))

def log_interval(x):
    assert x[0] > 0
    return log_rational(x[0])[0], log_rational(x[1])[1]

def xlogx(x):
    assert x[0] >= 0
    if x == const(0):
        return const(0)
    return times(x, log_interval(x))

def sqrt5_expression(a, b):
    return plus(const(a), scaled(SQRT5, b))

def bounds(x, places=16):
    """Closed decimal enclosure, with exact directed integer rounding."""
    s = 10**places
    lo = x[0].numerator*s // x[0].denominator
    hi = -((-x[1].numerator*s)//x[1].denominator)
    def render(v):
        sign = '-' if v < 0 else ''
        v = abs(v)
        return sign + str(v//s) + '.' + str(v%s).zfill(places)
    return [render(lo), render(hi)]

def bits(x):
    return times(x, (1/LOG2[1], 1/LOG2[0]))

def squared_fourier_sum(weights, a, t):
    # Exact |sum_x w_x zeta^(-2*a*x*x-t*x)|^2=A+B sqrt(5).
    A, B = Q(sum(w*w for w in weights)), Q(0)
    # 2*cos(2*pi*r/5), with exact rational + rational*sqrt(5).
    cos2 = [(Q(2), Q(0)), (-Q(1, 2), Q(1, 2)),
            (-Q(1, 2), -Q(1, 2)), (-Q(1, 2), -Q(1, 2)),
            (-Q(1, 2), Q(1, 2))]
    for x in range(5):
        for y in range(x):
            r = (2*a*(x*x-y*y)+t*(x-y)) % 5
            c, s = cos2[r]
            A += weights[x]*weights[y]*c
            B += weights[x]*weights[y]*s
    return A, B

def verify_diagonal_pure(weights):
    assert len(weights) == 5 and all(isinstance(w, int) and w >= 0 for w in weights)
    norm2 = sum(w*w for w in weights)
    assert norm2 > 0
    # The pure density is ww^T/norm2 on the |xx> subspace. Its partial
    # traces are diag(w_x^2/norm2), so the following H is the exact entropy.
    H = const(0)
    for w in weights:
        if w:
            H = plus(H, neg(xlogx(const(Q(w*w, norm2)))))
    measured = []
    for a in range(5):
        val = const(0)
        sumA = Q(0)
        sumB = Q(0)
        for t in range(5):
            A, B = squared_fourier_sum(weights, a, t)
            sumA += A
            sumB += B
            s = sqrt5_expression(A/norm2, B/norm2)
            assert s[0] > 0
            val = plus(val, scaled(xlogx(s), Q(1, 5)))
        assert sumA == 5*norm2 and sumB == 0
        assert val[0] > 0
        assert H[0] > val[1]  # The computational setting is the unique maximum.
        measured.append(val)
    trimmed = const(0)
    for v in measured:
        trimmed = plus(trimmed, v)
    quantum = scaled(H, 2)
    gap = plus(trimmed, neg(quantum))
    assert gap[0] > 0
    if weights == [20, 20, 1, 1, 1]:
        coarse = [(719274218695, 719274218696),
                  (339790731249, 339790731250),
                  (316889919807, 316889919808),
                  (243964476571, 243964476572)]
        for interval, (lo, hi) in zip([H] + measured[:3], coarse):
            assert Q(lo, 10**12) <= interval[0] <= interval[1] <= Q(hi, 10**12)
        assert gap[0] > Q(1, 50)
    return {
        'integer_amplitudes_on_00_11_22_33_44': weights,
        'normalization_squared': norm2,
        'Schmidt_rank': sum(w > 0 for w in weights),
        'computational_information_nats': bounds(H),
        'quadratic_setting_information_nats': [bounds(v) for v in measured],
        'computational_information_bits': bounds(bits(H)),
        'quadratic_setting_information_bits': [bounds(bits(v)) for v in measured],
        'trimmed_ECQC_score_bits': bounds(bits(trimmed)),
        'quantum_mutual_information_bits': bounds(bits(quantum)),
        'violation_nats': bounds(gap),
        'violation_bits': bounds(bits(gap)),
    }

def run():
    bell = verify_diagonal_pure([1, 1, 0, 0, 0])
    full = verify_diagonal_pure([20, 20, 1, 1, 1])
    return {
        'status': 'PASS',
        'method': 'integer sqrt brackets, Fraction arithmetic, log atanh series with geometric tail',
        'log_terms': TERMS,
        'sqrt5_decimal_bracket_digits': DIGITS,
        'sqrt5_lower_integer_numerator': root_floor,
        'sqrt5_bracket_denominator': SCALE,
        'decimal_intervals_are_outward_rounded': True,
        'embedded_Bell_state': bell,
        'full_Schmidt_rank_state': full,
        'scope': 'Independent rigorous entropy intervals for the two explicit pure states. '
                 'MUB and Born-law derivations are also given in the paper; '
                 'the first checker separately reconstructs the actual d=5 bases and Bell density.'
    }

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
