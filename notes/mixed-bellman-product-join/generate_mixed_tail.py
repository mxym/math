#!/usr/bin/env python3
"""Discover rational supporting points; exact interval decisions certify cells."""
from fractions import Fraction as F
from pathlib import Path
import json
import math
from scipy.optimize import minimize
from mixed_tail_core import (ALPHA, BETA, TOTAL, CUTOFF, POINT_DENOMINATOR,
                             coefficients, cell_endpoints, tail_bound)


def discover_point(r, z):
    a, b, c, a4, d4 = [float(q) for q in coefficients(r, float(z))]
    alpha, beta = float(ALPHA), float(BETA)
    def objective(p):
        h, j = (r+1)*p[0], p[1]
        x = h+r*(1+float(z))*j
        value = math.log(x)-alpha*(a*h*h+b*h*j+c*j*j)-beta*(a4*h**4+d4*j**4)
        gh = 1/x-alpha*(2*a*h+b*j)-4*beta*a4*h**3
        gj = r*(1+float(z))/x-alpha*(b*h+2*c*j)-4*beta*d4*j**3
        return -value, [-gh*(r+1), -gj]
    initial = [min(1, 2.8/math.sqrt(r+1)), min(1, 1/math.sqrt(r))]
    initial[0] = max(2/(r+1), initial[0])
    result = minimize(objective, initial, jac=True, bounds=[(2/(r+1), 1), (0, 1)],
                      method="L-BFGS-B", options={"ftol": 1e-14, "gtol": 1e-10, "maxiter": 1000})
    h = F(round((r+1)*result.x[0]*POINT_DENOMINATOR), POINT_DENOMINATOR)
    j = F(round(result.x[1]*POINT_DENOMINATOR), POINT_DENOMINATOR)
    return min(F(r+1), max(F(2), h)), min(F(1), max(F(0), j))


def main():
    rows = []
    worst = None
    for r in range(1, CUTOFF):
        stack = [(0, 0)]
        count = 0
        while stack:
            index, depth = stack.pop()
            left, right = cell_endpoints(index, depth)
            h, j = discover_point(r, (left+right)/2)
            bound = tail_bound(r, left, right, h, j)
            if bound is not None and bound < F(-1, 10000000):
                rows.append([r, index, depth, int(h*POINT_DENOMINATOR), int(j*POINT_DENOMINATOR)])
                count += 1
                if worst is None or bound > worst[0]:
                    worst = (bound, rows[-1])
            else:
                if depth >= 24:
                    raise RuntimeError(f"tail could not be certified at r={r}, cell={index}/{2**depth}, bound={bound}")
                stack.extend([(2*index+1, depth+1), (2*index, depth+1)])
        if r % 10 == 0 or r <= 5:
            print(json.dumps({"r": r, "cells": count, "total_cells": len(rows)}), flush=True)
    path = Path(__file__).resolve().parent / "mixed_tail_certificate.json"
    path.write_text(json.dumps({"schema": 1, "alpha": str(ALPHA), "beta": str(BETA),
                                "cutoff": CUTOFF, "point_denominator": POINT_DENOMINATOR,
                                "cells": rows}, separators=(",", ":"))+"\n")
    print(json.dumps({"cells": len(rows), "worst_bound_float_for_display": float(worst[0]),
                      "worst_cell": worst[1], "certificate": str(path)}), flush=True)


if __name__ == "__main__":
    main()
