"""Floating sign/factor diagnostics, explicitly not a proof certificate."""
from hashlib import sha256
import json
from pathlib import Path

import numpy as np

from covariance_probe import (BASE, BASIS, assignment, balanced_value,
                              covariance_hessian)


def main():
    step = .0002
    cases = [('regular', np.eye(3) / 12),
             ('generic', np.array([[.13, .015, -.01],
                                   [.015, .07, .02], [-.01, .02, .05]]))]
    rows = []
    wrong_price_detected = False
    for name, covariance in cases:
        value, hessian, prices, _ = covariance_hessian(covariance)

        def fixed_price_value(matrix):
            scores = BASE @ np.linalg.cholesky(matrix)
            masses, _, moments = assignment(scores, prices)
            return float(np.sum(scores * moments) + (.25 - masses) @ prices)

        for index, direction in enumerate(BASIS):
            plus = balanced_value(covariance + step * direction)[0]
            minus = balanced_value(covariance - step * direction)[0]
            finite_difference = (plus + minus - 2 * value) / step**2
            unbalanced = (fixed_price_value(covariance + step * direction)
                          + fixed_price_value(covariance - step * direction)
                          - 2 * value) / step**2
            error = abs(finite_difference - hessian[index, index])
            if error > 5e-4:
                raise RuntimeError('Hessian diagnostic disagrees: ' + str(error))
            if abs(unbalanced - hessian[index, index]) > .1:
                wrong_price_detected = True
            if abs(finite_difference - 4 * hessian[index, index]) < .1:
                raise RuntimeError('Incorrect Hessian factor was not detected')
            rows.append({'case': name, 'direction': index,
                         'analytic': float(hessian[index, index]),
                         'rebalanced_finite_difference': finite_difference,
                         'fixed_price_finite_difference': unbalanced,
                         'absolute_discrepancy': error})
    if not wrong_price_detected:
        raise RuntimeError('Omitting the price correction was not detected')
    print(json.dumps({'diagnostic_pass': True, 'proof_certificate': False,
                      'scope': 'floating Hessian signs, factors and price adjustment only',
                      'step': step, 'wrong_factor_detected': True,
                      'omitted_price_adjustment_detected': wrong_price_detected,
                      'sources': {name: sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('covariance_probe.py',
                                               'covariance_diagnostic.py',
                                               'stationary_search.py')},
                      'records': rows}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
