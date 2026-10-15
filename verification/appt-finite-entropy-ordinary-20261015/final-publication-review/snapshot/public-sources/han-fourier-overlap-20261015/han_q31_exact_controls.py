"""Finite consistency controls for the Han Q3.1 counterexample.

Standard library only.  Full integer Walsh transforms and physical edge counts
are compared to an independently updated rational recurrence for depths 0..4.
This is neither an arbitrary-depth proof nor an independent ordinary review.
"""
from __future__ import annotations

import datetime as dt
from fractions import Fraction as F
import json
from pathlib import Path


def walsh(values: list[int]) -> list[int]:
    out = values.copy()
    width = 1
    while width < len(out):
        for base in range(0, len(out), 2 * width):
            for j in range(base, base + width):
                a, b = out[j], out[j + width]
                out[j], out[j + width] = a + b, a - b
        width *= 2
    return out


def main() -> None:
    truth = [1, -1]
    p, influence, sum_variance = F(1, 2), F(1), F(0)
    gates: list[str] = []
    checks: list[dict] = []
    for depth in range(5):
        n, size = 1 << depth, len(truth)
        assert size == 1 << n and set(truth) <= {-1, 1}
        mean = 2 * p - 1
        walsh_numerators = walsh(truth)
        assert sum(x * x for x in walsh_numerators) == size * size
        assert F(sum(truth), size) == mean
        assert F(1, 4) <= p <= F(3, 4)
        predicted_l1_over_i = 2 * sum_variance + 4 * abs(mean)
        coordinates = []
        for i in range(n):
            mask = 1 << i
            lower = [s for s in range(size) if not (s & mask)]
            edge_count = sum(truth[x] != truth[x ^ mask] for x in range(size))
            physical_i = F(edge_count, size)
            fourier_i_num = sum(walsh_numerators[s | mask] ** 2 for s in lower)
            fourier_i = F(fourier_i_num, size * size)
            overlap_num = sum(abs(walsh_numerators[s] * walsh_numerators[s | mask]) for s in lower)
            overlap = F(overlap_num, size * size)
            assert physical_i == fourier_i == influence and influence > 0
            assert 4 * overlap / influence == predicted_l1_over_i
            assert overlap / influence >= F(3 * depth, 8)
            # Direct restricted truth tables supply a third way to obtain 4A.
            plus = [truth[x] for x in range(size) if not (x & mask)]
            minus = [truth[x] for x in range(size) if x & mask]
            wp, wm = walsh(plus), walsh(minus)
            restricted_l1 = F(sum(abs(a*a - b*b) for a, b in zip(wp, wm)), (size // 2) ** 2)
            assert restricted_l1 == 4 * overlap
            coordinates.append({'coordinate': i, 'physical_influence': str(physical_i),
                                'fourier_influence': str(fourier_i), 'A_over_I': str(overlap / influence)})
        checks.append({'depth': depth, 'number_of_variables': n, 'truth_table_entries': size,
                       'gates_bottom_to_top': gates.copy(), 'mean': str(mean),
                       'all_coordinates_checked': coordinates,
                       'predicted_L1_over_I': str(predicted_l1_over_i)})
        if depth == 4:
            break
        sum_variance += 1 - mean * mean
        kind = 'OR' if p <= F(1, 2) else 'AND'
        gates.append(kind)
        beta = 1 - p if kind == 'OR' else p
        influence *= beta
        p = 2*p - p*p if kind == 'OR' else p*p
        if kind == 'OR':
            truth = [(a+b-a*b+1)//2 for a in truth for b in truth]
        else:
            truth = [(a+b+a*b-1)//2 for a in truth for b in truth]
    result = {'created_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
              'scope': 'One explicit homogeneous read-once formula per depth 0..4. All coordinates and complete truth tables. Integer and rational checks only; no entropy floating approximations.',
              'proof_scope': 'Finite consistency checks, not the arbitrary-depth induction and not an independent review.',
              'passed': True, 'checks': checks}
    path = Path(__file__).with_name('HAN_Q31_EXACT_CONTROLS.json')
    path.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'passed': True, 'depths': 5, 'total_coordinates_checked': sum(len(c['all_coordinates_checked']) for c in checks), 'output': str(path)}))


if __name__ == '__main__':
    main()
