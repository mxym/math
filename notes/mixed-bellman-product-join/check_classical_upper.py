#!/usr/bin/env python3
"""Exact intervals for two existing unrestricted asymptotic upper constants.

Uses rational Taylor/alternating-series bounds only. The geometric inequalities
and their dimension limit are written in literature.md.
"""
from fractions import Fraction as F
from math import factorial
import json
import argparse
from pathlib import Path


def atan_interval(x, n=40):
    # Terms decrease for 0 < x < 1. Consecutive partial sums enclose atan x.
    s = sum(((-1)**j * x**(2*j+1) / (2*j+1) for j in range(n)), F(0))
    t = s + (-1)**n * x**(2*n+1) / (2*n+1)
    return min(s, t), max(s, t)


def rational_record(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Optional JSON output; no supplied file is changed by default.')
    args = parser.parse_args()
    a_l, a_u = atan_interval(F(1, 5))
    b_l, b_u = atan_interval(F(1, 239))
    # Machin's identity follows from the tangent addition formula and angles.
    pi_l, pi_u = 16*a_l - 4*b_u, 16*a_u - 4*b_l
    m = 80
    e_l = sum((F(1, factorial(j)) for j in range(m+1)), F(0))
    # Remaining term ratios are <= 1/(m+2).
    e_u = e_l + F(m+2, (m+1)*factorial(m+1))
    c_l, c_u = pi_l*e_l/2, pi_u*e_u/2
    target_l, target_u = F(4269867111336, 10**12), F(4269867111337, 10**12)
    if not target_l < c_l < c_u < target_u:
        raise ValueError("Requested enclosure not certified")
    # pi e / 2 < e^(3/2) iff pi^2 < 4e; this is certified exactly.
    if not pi_u**2 < 4*e_l:
        raise ValueError("Strict comparison with LYZ root not certified")
    data = {
        "status": "passed",
        "method": "Machin alternating-series intervals; exponential Taylor interval",
        "pi_interval": [rational_record(pi_l), rational_record(pi_u)],
        "e_interval": [rational_record(e_l), rational_record(e_u)],
        "pi_e_over_two_interval": [rational_record(c_l), rational_record(c_u)],
        "decimal_enclosure": ["4.269867111336", "4.269867111337"],
        "strict_comparison": "pi_upper^2 < 4 e_lower",
        "scope": "existing classical upper constants; no new projection-volume theorem",
    }
    if args.output:
        args.output.write_text(json.dumps(data, indent=2)+"\n")
    print("PASS: 4.269867111336 < pi*e/2 < 4.269867111337 < e^(3/2)")


if __name__ == "__main__":
    main()
