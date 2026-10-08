#!/usr/bin/env python3
"""Finite rational diagnostics only; not a proof of Gaussian analysis."""
from fractions import Fraction as F
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    edge_cases = 0
    radial_cases = 0
    for k in range(2, 13):
        count = k*(k-1)//2
        for seed in range(1, 7):
            w = [F((i+seed) % 7, 1+(i % 3)) for i in range(count)]
            ell = [F(1+(i*seed) % 9, 2+(i % 4)) for i in range(count)]
            W = sum(w)
            C = sum(a*b*b for a, b in zip(w, ell))
            S = sum(a*b for a, b in zip(w, ell))
            variance = sum(w[i]*w[j]*(ell[i]-ell[j])**2
                           for i in range(count) for j in range(i+1, count))
            need(W*C-S*S == variance >= 0, 'Weighted variance identity')
            edge_cases += 1
    for a in range(1, 7):
        for b in range(4):
            for case in range(1, 61):
                ell = case//12-2
                numerator = 1+(case-1)%12
                t = F(numerator, 13)
                h = ell*t-a*t*t-b*t**3
                hp = ell-2*a*t-3*b*t*t
                D = a*t*t+2*b*t**3
                need((t*hp-h)/t**2 == -D/t**2 <= 0, 'Quotient sign identity')
                need(h <= ell*t, 'Arbitrary-initial-slope control value')
                radial_cases += 1
    # h=t satisfies h(0)=0 and t*h'=h but lacks h'(0)=0.
    t = F(1, 2)
    need(t*1 == t and t > 0, 'Missing-derivative countermodel')
    # h=t^2 has zero initial derivative but violates t*h'<=h.
    need(t*(2*t) > t*t > 0, 'Missing-differential-inequality countermodel')
    print(json.dumps({'status': 'PASS', 'weighted_variance_cases': edge_cases,
                      'radial_identity_cases': radial_cases,
                      'negative_countermodels': 2,
                      'scope': 'finite rational diagnostics; no Gaussian endpoint checking',
                      'analytic_endpoint_checked': False}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
