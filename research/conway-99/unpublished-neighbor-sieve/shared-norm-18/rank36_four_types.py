"""Check Fano square incidences and the rank-36 short-shell identity."""
from itertools import combinations
from pathlib import Path
import runpy


def check_squares():
    sites = range(1, 8)
    neighbors = {u: {v for v in sites if (u & v).bit_count() % 2} for u in sites}
    for a, b in combinations(sites, 2):
        assert len(neighbors[a] & neighbors[b]) == 2
        assert len(set(sites) - neighbors[a] - neighbors[b]) == 1
    squares = 99 * 84 // 4
    assert squares == 2079
    assert 21 * 198 == 2 * squares


def check_theta_identity():
    source = Path(__file__).resolve().parents[2] / "maximal-marked-lattice" / "verify.py"
    basis = runpy.run_path(str(source))["fourier_basis"]()
    for i in reversed(range(15)):
        x, y = basis[i]
        for j in range(i + 1, 15):
            coefficient = x[j]
            if coefficient:
                u, v = basis[j]
                x = [a-coefficient*b for a, b in zip(x, u)]
                y = [a-coefficient*b for a, b in zip(y, v)]
        assert x[:15] == [int(i == j) for j in range(15)]
        basis[i] = x, y

    for i in (0, *range(7, 15)):
        x, y = basis[i]
        y = [7**7 * a for a in y]
        left = 57967*x[7] + 17150*x[8] + 4459*x[9] + 637*x[10]
        right = (343*(68*y[2] + 3*y[3]) + 119021*y[1] + 49*x[12]
                 - 32002243*x[0] - 4079299*y[0])
        assert left == right


def check_bounds():
    for norm_six, residual in ((41058, 5465362), (44804, 9319996)):
        lower = 343*(68*462 + 3*norm_six) - 32002243 - 4079299
        assert lower - 57967*198 == residual > 0
    assert 4459*2090 < 9319996 <= 4459*2092
    assert 17150*542 < 9319996 <= 17150*544


if __name__ == "__main__":
    check_squares()
    check_theta_identity()
    check_bounds()
    print("Fano square cap 198. Nine theta directions verified.")
    print("At rank 36, absence of norm 20 forces 17150 N16 + 4459 N18 >= 9319996.")
