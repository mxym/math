"""Replay both exact identities for one rank-36 three-unit exclusion."""
from fractions import Fraction as Q
from pathlib import Path
import runpy

from rank36_three_types import P, UNIT, short_equations


def short_identity():
    keys, rows = short_equations()
    allowed = {(0, 26), (1, 25), (1, 27)}
    target = {
        (0, 0): -266, (0, 22): 12, (3, 33): 24,
        (3, 35): 26, (4, 44): 18, (2, 32): 8,
    }
    weights = (-266, 0, 168, -116, 36, 12, -8, 0, 18)
    assert len(rows) == len(weights)
    pivots = [next(v for v in row if v) for row in rows]
    for i, key in enumerate(keys):
        if key not in UNIT - allowed:
            actual = sum(Q(w * row[i], pivot)
                         for w, row, pivot in zip(weights, rows, pivots))
            assert actual == target.get(key, 0), key
    assert set(target) <= set(keys) - (UNIT - allowed)
    assert all((9*t - 11*a*a) % 7 for a, t in target if (a, t) != (0, 0))


def scalar_identity():
    source = Path(__file__).resolve().parents[2] / "maximal-marked-lattice" / "verify.py"
    basis = runpy.run_path(str(source))["fourier_basis"]()
    # Fully row-reduce the first fifteen coefficients of the cusp pairs.
    for i in reversed(range(15)):
        x, y = basis[i]
        for j in range(i + 1, 15):
            z = x[j]
            if z:
                u, v = basis[j]
                x = [a-z*b for a, b in zip(x, u)]
                y = [a-z*b for a, b in zip(y, v)]
        assert x[:15] == [int(i == j) for j in range(15)]
        basis[i] = x, y
    for i in [0, *range(7, 15)]:
        x, y = basis[i]
        y = [v * 7**7 for v in y]   # 7^(11 - (44 - 36)/2)
        lhs = sum(a*x[j] for j, a in enumerate((35, 25, 11, 8, 3, 1), 7))
        assert lhs == 343*(y[2] + 988*y[0] + 43*y[1]) - 1988*x[0]


if __name__ == "__main__":
    short_identity()
    scalar_identity()
    lower = 343*(462 + 988) - 1988 - 35*990
    assert lower == 460712
    assert 4*lower == 1842848 > 266*P == 638932
    print("Exact short and scalar identities verified: 1842848 > 638932.")
