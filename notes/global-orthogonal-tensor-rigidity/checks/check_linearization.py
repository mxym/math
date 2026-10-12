"""Exact finite checks of the derivative kernel; no analytic claims."""
from fractions import Fraction as Q
from itertools import product


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def rank(rows, columns):
    pivots = {}
    for row in rows:
        row = {i: Q(v) for i, v in enumerate(row) if v}
        while row:
            p = min(row)
            if p not in pivots:
                scale = row[p]
                pivots[p] = {i: v / scale for i, v in row.items()}
                break
            scale = row[p]
            for i, v in pivots[p].items():
                row[i] = row.get(i, Q(0)) - scale * v
                if not row[i]:
                    del row[i]
    require(all(p < columns for p in pivots), "rank column range")
    return len(pivots)


def zero(m):
    return [[Q(0) for _ in range(m)] for _ in range(m)]


def mul(a, b):
    m = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(m))
             for j in range(m)] for i in range(m)]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def neg(a):
    return [[-v for v in row] for row in a]


def comm(a, b):
    return add(mul(a, b), neg(mul(b, a)))


def canonical(m):
    xs = [zero(m) for _ in range(m)]
    for r in range(m):
        xs[r][r][r] = Q(1)
    return xs


def basis(m):
    out = []
    for r in range(m):
        for i in range(m):
            for j in range(i, m):
                h = [zero(m) for _ in range(m)]
                h[r][i][j] = h[r][j][i] = Q(1)
                out.append(h)
    return out


def flatten(a):
    return [v for row in a for v in row]


def defects(h, include_b=True, include_spatial=True):
    """Differentiate the actual polynomial curl for g(a)=a+a²/2.

    The constant and first spatial coefficients are computed by matrix
    multiplication, without using the simplified commutator formula.
    """
    m = len(h)
    x = canonical(m)
    out = []
    for i, r, s in product(range(m), repeat=3):
        out.append(h[r][i][s] - h[s][i][r])
    if include_spatial:
        ds = {}
        for r, t in product(range(m), repeat=2):
            ds[r, t] = add(
                add(mul(h[r], x[t]), mul(x[r], h[t])),
                add(mul(h[t], x[r]), mul(x[t], h[r])))
        for t, i, r, s in product(range(m), repeat=4):
            # twice the differentiated linear spatial curl coefficient
            out.append(ds[r, t][i][s] - ds[s, t][i][r])
    if include_b:
        b = zero(m)
        for r in range(m):
            b = add(b, add(mul(x[r], h[r]), mul(h[r], x[r])))
        out += flatten(b)
    return out


def rotated_tensor(m):
    # An exact rational orthogonal Householder reflection.
    v = [Q(i + 1) for i in range(m)]
    vv = sum(t * t for t in v)
    u = [[Q(i == j) - 2 * v[i] * v[j] / vv
          for j in range(m)] for i in range(m)]
    ut = list(map(list, zip(*u)))
    require(mul(ut, u) == [[Q(i == j) for j in range(m)]
                           for i in range(m)], "Householder orthogonality")
    return [[[sum(u[r][a] * u[i][a] * u[j][a] for a in range(m))
              for j in range(m)] for i in range(m)] for r in range(m)]


def check_zeros(xs):
    m = len(xs)
    b = zero(m)
    for x in xs:
        b = add(b, mul(x, x))
    require(b == [[Q(i == j) for j in range(m)] for i in range(m)],
            "normalization")
    require(all(xs[r][i][s] == xs[s][i][r]
                for r, i, s in product(range(m), repeat=3)),
            "tensor compatibility")
    require(all(comm(x, y) == zero(m) for x in xs for y in xs),
            "commutators")


def main():
    for m in range(1, 7):
        bs = basis(m)
        columns = [defects(h) for h in bs]
        rows = list(zip(*columns))
        actual = rank(rows, len(bs))
        expected = len(bs) - m * (m - 1) // 2
        require(actual == expected, f"kernel dimension at m={m}")
        for i in range(m):
            for j in range(i + 1, m):
                # d/dt sum (exp(tK)e_a)^tensor3, K_ji=1, K_ij=-1.
                h = [zero(m) for _ in range(m)]
                for r, a, b in product(range(m), repeat=3):
                    inds = sorted((r, a, b))
                    if inds == sorted((i, i, j)):
                        h[r][a][b] = Q(1)
                    elif inds == sorted((i, j, j)):
                        h[r][a][b] = Q(-1)
                require(not any(defects(h)), "rotation generator not in kernel")
        check_zeros(rotated_tensor(m))
        # Removing normalization always leaves at least m extra directions.
        cols = [defects(h, include_b=False) for h in bs]
        r_without_b = rank(list(zip(*cols)), len(bs))
        require(r_without_b < actual, "missing normalization not detected")
        if m >= 3:
            cols = [defects(h, include_spatial=False) for h in bs]
            require(rank(list(zip(*cols)), len(bs)) < actual,
                    "missing first spatial curl not detected")
        print(f"m={m}: rank={actual}, kernel={len(bs)-actual}; "
              "rotation, nonlinear zero-set, negative controls PASS")
    # Normalization + commutation alone do not imply Jacobian compatibility.
    bad = [zero(2), zero(2)]
    bad[0] = [[Q(1), Q(0)], [Q(0), Q(1)]]
    require(add(mul(bad[0], bad[0]), mul(bad[1], bad[1]))
            == [[Q(1), Q(0)], [Q(0), Q(1)]], "bad example B")
    require(comm(*bad) == zero(2), "bad example commutation")
    require(bad[0][1][1] != bad[1][1][0], "bad compatibility not detected")
    print("ALL EXACT LINEARIZATION CHECKS PASSED")


if __name__ == "__main__":
    main()
