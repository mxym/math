#!/usr/bin/env python3
"""Exact finite geometry controls, not a test for the analytic endpoint.

Compares an actual preorder placement against a nonrecursive closed formula.
Uniform all-height algebra is proved separately in formal/VariableTree.lean.
Only Python's standard library is used; optimization cannot disable checks.
"""
from fractions import Fraction as F
import json


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def closed_span(b, d, L, g):
    power = (2 * b) ** (d - 1)
    return F(power * (b * L + (b - 1) * g)) + F(
        (3 * b - 1) * g * (power - 1), 2 * b - 1)


def preorder(b, d, L, g):
    """Return actual windows (start,length,local_end), starting at zero."""
    windows = []

    def visit(height, start):
        cursor = start
        for child in range(b):
            length = L if height == 1 else g + int(closed_span(b, height - 1, L, g))
            slot = len(windows)
            windows.append(None)
            cursor += length
            if height > 1:
                cursor = visit(height - 1, cursor + g)
            windows[slot] = (start if child == 0 else edge_start, length, cursor)
            if child + 1 < b:
                cursor += g
                edge_start = cursor
        return cursor

    total = visit(d, 0)
    return total, windows


def check_row(row):
    b, d, L, g = (row[name] for name in ('b', 'd', 'L', 'g'))
    need(b >= 2 and d >= 1 and L >= 0 and g >= 0, 'row domain')
    total, windows = preorder(b, d, L, g)
    expected = closed_span(b, d, L, g)
    need(expected.denominator == 1, 'integral closed span')
    need(row['span'] == total == expected, 'preorder/closed span mismatch')
    K = sum(b ** r for r in range(1, d + 1))
    need(row['edges'] == len(windows) == K, 'edge count mismatch')
    need(K * (b - 1) == b ** (d + 1) - b, 'geometric identity')
    need(K <= 2 * b ** d, 'geometric bound')
    need(total + 2 * g <= b * (2 * b) ** (d - 1) * (L + 2 * g), 'first span bound')
    need(total <= (2 * b) ** d * (L + 2 * g), 'second span bound')
    for i, (start, length, local_end) in enumerate(windows):
        need(length >= L and local_end - start <= 2 * length, 'local subtree bound')
        if i:
            previous_start, previous_length, _ = windows[i - 1]
            need(start == previous_start + previous_length + g, 'preorder gap')


def main():
    rows = []
    for b in range(2, 6):
        for d in range(1, 5):
            for L in range(5):
                for g in range(4):
                    row = dict(b=b, d=d, L=L, g=g,
                               span=int(closed_span(b, d, L, g)),
                               edges=sum(b ** r for r in range(1, d + 1)))
                    check_row(row)
                    rows.append(row)
    # Corrupted input must actually be rejected by the same checker.
    bad = dict(rows[-1], span=rows[-1]['span'] + 1)
    try:
        check_row(bad)
    except RuntimeError:
        pass
    else:
        raise RuntimeError('corrupted span accepted')
    bad = dict(rows[-1], edges=rows[-1]['edges'] - 1)
    try:
        check_row(bad)
    except RuntimeError:
        pass
    else:
        raise RuntimeError('corrupted edge count accepted')

    # ln(2)=2 atanh(1/3). Its positive remainder is bounded geometrically.
    terms = 12
    partial = 2 * sum((F(1, (2 * j + 1) * 3 ** (2 * j + 1))
                       for j in range(terms)), F(0))
    tail = F(2, (2 * terms + 1) * 3 ** (2 * terms + 1)) / (1 - F(1, 9))
    need(partial + tail < F(3, 4), 'rigorous ln2 guard')
    need(6 - 4 * (partial + tail) > 3, 'kappa guard')
    entropy = 0
    for P in range(1, 65):
        for ell in range(2, 25):
            m = P * (3 + 2 ** (2 * ell + 3))
            need(m + 5 <= 16 * P * 2 ** (2 * ell), 'line-count prefactor')
            need(2 * m * m + 1 <= 20 * (m + 5) ** 2, 'boundary strata bound')
            need(20 * (16 * P * 2 ** (2 * ell)) ** 2 ==
                 5120 * P * P * 2 ** (4 * ell), 'entropy coefficient')
            entropy += 1
    print(json.dumps({'status': 'PASS', 'preorder_cases': len(rows),
        'placed_windows': sum(row['edges'] for row in rows),
        'entropy_controls': entropy, 'corruptions_rejected': 2,
        'ln2_upper_rational': str(partial + tail),
        'scope': 'finite algebra/geometry controls; not the infinite analytic theorem'},
        indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
