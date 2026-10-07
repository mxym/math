"""Exact polynomial and tensor identities for the independent global theorem."""
from fractions import Fraction as Q
from itertools import product
from random import Random
from check_linearization import zero, mul, add, neg, comm, require


def pol_add(p, q):
    out = p.copy()
    for k, v in q.items():
        out[k] = out.get(k, Q(0)) + v
        if not out[k]:
            del out[k]
    return out


def pol_scale(p, s):
    return {k: v*s for k, v in p.items() if v*s}


def pol_mul(p, q):
    out = {}
    for a, x in p.items():
        for b, y in q.items():
            k = tuple(i+j for i, j in zip(a, b))
            out[k] = out.get(k, Q(0)) + x*y
    return {k: v for k, v in out.items() if v}


def square(p):
    return pol_mul(p, p)


def binary_identities():
    vs = [{tuple(int(i == j) for i in range(4)): Q(1)} for j in range(4)]
    a, b, c, d = vs
    x = pol_add(a, c)
    y = pol_add(b, pol_scale(d, Q(1, 3)))
    z = pol_add(pol_scale(a, -1), pol_scale(c, Q(1, 3)))
    w = pol_add(pol_scale(b, -1), d)
    norm = pol_add(pol_add(square(x), pol_scale(square(y), 3)),
                   pol_add(pol_scale(square(z), 3), square(w)))
    expected = pol_add(pol_scale(pol_add(square(a), square(b)), 4),
                       pol_scale(pol_add(square(c), square(d)), Q(4, 3)))
    require(norm == expected, "binary tensor norm identity")
    k = pol_add(pol_add(pol_mul(x, z), pol_mul(y, w)),
                pol_scale(pol_add(square(y), square(z)), -1))
    expected_k = pol_scale(pol_add(
        pol_scale(pol_add(square(c), square(d)), Q(1, 9)),
        pol_scale(pol_add(square(a), square(b)), -1)), 2)
    require(k == expected_k, "binary commutator polynomial")
    lhs = pol_add(square(pol_add(pol_mul(a, c), pol_scale(pol_mul(b, d), -1))),
                  square(pol_add(pol_mul(a, d), pol_mul(b, c))))
    rhs = pol_mul(pol_add(square(a), square(b)),
                  pol_add(square(c), square(d)))
    require(lhs == rhs, "four-angle amplitude identity")
    corrupted = pol_scale(expected_k, Q(2))
    require(k != corrupted, "wrong commutator coefficient not detected")


def random_symmetric_tensor(m, rng):
    values = {}
    t = [[[Q(0) for _ in range(m)] for _ in range(m)] for _ in range(m)]
    for i, j, k in product(range(m), repeat=3):
        key = tuple(sorted((i, j, k)))
        if key not in values:
            values[key] = Q(rng.randint(-4, 4), rng.randint(1, 5))
        t[i][j][k] = values[key]
    return t


def block_check(m, rng):
    mu = [Q(rng.randint(-4, 4), 5) for _ in range(m-1)]
    xs = [zero(m) for _ in range(m)]
    xs[0][0][0] = Q(3)
    for i in range(1, m):
        xs[0][i][i] = xs[i][0][i] = xs[i][i][0] = mu[i-1]
    rest = random_symmetric_tensor(m-1, rng)
    for i, j, k in product(range(1, m), repeat=3):
        xs[i][j][k] = rest[i-1][j-1][k-1]
    for i in range(1, m):
        c = comm(xs[0], xs[i])
        require(c[i][0] == mu[i-1]*(mu[i-1]-3), "splitting commutator")
    for i, j in product(range(1, m), repeat=2):
        block = [row[1:] for row in comm(xs[i], xs[j])[1:]]
        correction = zero(m-1)
        correction[i-1][j-1] += mu[i-1]*mu[j-1]
        correction[j-1][i-1] -= mu[i-1]*mu[j-1]
        require(block == add(comm(rest[i-1], rest[j-1]), correction),
                "compression commutator identity")
    mixed_sq = sum(xs[i][j][k]**2 for i, j, k in product(range(m), repeat=3)
                   if (i == 0 or j == 0 or k == 0) and (i, j, k) != (0, 0, 0))
    require(mixed_sq == 3*sum(v*v for v in mu), "mixed tensor norm")
    row_col_sq=4*sum(comm(xs[0],xs[i])[i][0]**2 for i in range(1,m))
    require(row_col_sq==4*sum(v*v*(v-3)**2 for v in mu),
            "aggregate skew-commutator norm")
    require(row_col_sq>=9*sum(v*v for v in mu),
            "aggregate spectral-gap estimate")
    # Independently expand the associator in scalar products.
    for r, s, i, j in product(range(m), repeat=4):
        expanded = sum(xs[r][i][k]*xs[s][k][j]
                       - xs[s][i][k]*xs[r][k][j] for k in range(m))
        require(expanded == comm(xs[r], xs[s])[i][j], "associator entries")


def main():
    binary_identities()
    rng = Random(101162)
    for m in range(2, 7):
        for _ in range(8):
            block_check(m, rng)
        print(f"m={m}: 8 exact splitting/compression/associator cases PASS")
    base = [[[Q(1), Q(0)], [Q(0), Q(-1)]],
            [[Q(0), Q(-1)], [Q(-1), Q(0)]]]
    r2 = sum(v*v for x in base for y in base for row in comm(x, y) for v in row)
    require(r2 == 16, "harmonic cubic residual squared")
    for t in (Q(1), Q(1, 2), Q(1, 17)):
        scaled = [[[t*v for v in row] for row in x] for x in base]
        actual = sum(v*v for x in scaled for y in scaled
                     for row in comm(x, y) for v in row)
        require(actual == 16*t**4, "sharpness homogeneity")
    print("Binary polynomial identities and negative control PASS")
    print("ALL EXACT GLOBAL ODECO CHECKS PASSED")


if __name__ == "__main__":
    main()
