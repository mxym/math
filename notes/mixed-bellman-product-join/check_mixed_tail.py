#!/usr/bin/env python3
"""Exact replay verification; neither SciPy nor floating point is used."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
from mixed_tail_core import (ALPHA, BETA, CUTOFF, POINT_DENOMINATOR, require,
                             cell_endpoints, tail_bound)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=Path(__file__).resolve().with_name('mixed_tail_certificate.json'),
                        help='Tail certificate (default: supplied sibling file).')
    parser.add_argument('--report', type=Path, help='Optional JSON report output.')
    args = parser.parse_args()
    path = args.certificate
    certificate = json.loads(path.read_text())
    require(certificate["schema"] == 1, "unsupported tail certificate schema")
    require(certificate["alpha"] == str(ALPHA) and certificate["beta"] == str(BETA), "potential constants differ")
    require(certificate["cutoff"] == CUTOFF and certificate["point_denominator"] == POINT_DENOMINATOR, "certificate scales differ")
    ranges = {r: [] for r in range(1, CUTOFF)}
    worst = None
    for row in certificate["cells"]:
        r, index, depth, hn, jn = row
        require(r in ranges and isinstance(index, int) and isinstance(depth, int), "invalid tail cell")
        require(0 <= depth <= 24 and 0 <= index < 2**depth, "invalid dyadic coordinates")
        left, right = cell_endpoints(index, depth)
        bound = tail_bound(r, left, right, F(hn, POINT_DENOMINATOR), F(jn, POINT_DENOMINATOR))
        require(bound is not None and bound < 0, f"failed tail supporting certificate: {row}")
        ranges[r].append((left, right))
        if worst is None or bound > worst[0]:
            worst = (bound, row)
    for r, cells in ranges.items():
        cursor = F(0)
        for left, right in sorted(cells):
            require(left == cursor, f"gap or overlap in r={r} tail coverage")
            cursor = right
        require(cursor == F(1, CUTOFF), f"incomplete r={r} tail coverage")
    require(worst[0] < F(-1, 100000000), "tail margin below claimed universal endpoint")
    report = {"status": "PASS", "all_integer_dimensions": "1<=r<200, s>=200",
                      "cells": len(certificate["cells"]), "maximum_depth": max(row[2] for row in certificate["cells"]),
                      "uniform_certified_upper_margin": "-1/100000000",
                      "worst_cell": worst[1], "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
