"""Exact rank-36 coclique tangent certificate."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import runpy

from flint import fmpq_mat
from rank36_three_types import P, UNIT, short_equations

E = {
    (0, 0): -148962, (0, 14): -3207, (0, 18): 6396,
    (0, 22): -648, (0, 24): -216, (2, 22): 3207,
    (2, 32): -11, (3, 33): -1296, (3, 35): -756, (4, 44): -1199,
}


def short_identity():
    keys, rows = short_equations()
    allowed = {(0, 18), (0, 24), (0, 26)}
    active = [i for i, key in enumerate(keys) if key not in UNIT - allowed]
    assert set(E) <= {keys[i] for i in active}
    plane = [[row[i] for i in active] for row in rows]
    target = [E.get(keys[i], 0) for i in active]
    assert fmpq_mat(plane + [target]).rank() == fmpq_mat(plane).rank() == 9


def scalar_identity():
    source = Path(__file__).resolve().parents[2] / "maximal-marked-lattice" / "verify.py"
    basis = runpy.run_path(str(source))["fourier_basis"]()
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
    dirs = [0, *range(7, 15)]
    # For determinant 49, anisotropy gives y_j = x_(7j).
    constraints = [[7**10*basis[i][1][j] - basis[i][0][7*j] for i in dirs]
                   for j in range(8)]
    form = [-1000, 8, -25, -11, -8, -3, -1, 0, 1]
    rational = lambda rows: [[str(v) for v in row] for row in rows]
    assert fmpq_mat(rational(constraints + [form])).rank() == fmpq_mat(rational(constraints)).rank() == 2


def multiplier():
    # True counts per H: at a nonzero seven-value, W averages 8 classes.
    def shell(a, t):
        return 8 if (9*t - 11*a*a) % 7 else 1

    y2 = defaultdict(int, {(0, 0): 1000})
    for j, c in zip(range(7, 13), (-8, 25, 11, 8, 3, 1)):
        for a, t, multiplicity in ((0, 2*j, 1), (3, 2*j+11, 2)):
            if t < 11*a or (a, t) in {(0, 16), (0, 20)}:
                continue
            y2[a, t] += c*multiplicity*shell(a, t)
    t = {k: 9*v for k,v in y2.items()}
    for k, c in [((0, 14), 18), ((0, 0), 24500-9*462), ((2, 22), -9*41-700)]:
        t[k] = t.get(k, 0) + c
    m = {k: 3*t.get(k, 0)+E.get(k, 0) for k in set(t)|set(E)}
    assert {k:v for k,v in m.items() if v} == {
        (0, 0): -60936, (0, 18): 8772, (0, 14): -3369,
        (2, 32): -11, (3, 35): -324, (4, 44): -1199,
    }
    assert P == 2402
    assert -60936 + 8772*Q(16166,P) == Q(-2280060,1201) < 0


if __name__ == "__main__":
    short_identity()
    scalar_identity()
    multiplier()
    print("Exact coclique tangent contradiction: 3T <= -2280060/1201 < 0.")
