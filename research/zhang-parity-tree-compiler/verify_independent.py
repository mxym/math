"""Independent direct polarization and maximal-minor residue checks.

This verifier does not import the prototype. It is deliberately exponential
only in the tiny test dimensions and implements the older all-minors descent.
"""

from itertools import combinations, permutations
from functools import reduce
from operator import xor


def mul(x, y):
    terms = [i+j for i in range(x.bit_length()) if (x >> i) & 1
             for j in range(y.bit_length()) if (y >> j) & 1]
    return reduce(xor, (1 << r for r in terms), 0)


def prod(a):
    return reduce(mul, a, 1)


def det(a):
    return reduce(xor, (prod(a[i][j] for i, j in enumerate(p))
                        for p in permutations(range(len(a)))), 0)


def val(p):
    assert p
    return (p & -p).bit_length() - 1


def poly_form(n, j, support, v):
    out = 0
    for S in support:
        coords = [i for i in range(n) if (S >> i) & 1]
        if len(coords) == j:
            out ^= det([[vec[i] for i in coords] for vec in v])
    return out


def contract(n, j, terms, a):
    e = [[int(i == t) for t in range(n)] for i in range(n)]
    return [[poly_form(n, j, terms, a + [x, y]) for x in e] for y in e]


def minor(a, rows, cols):
    return det([[a[i][j] for j in cols] for i in rows])


def kernel_by_cramer(a, r):
    n = len(a)
    choices = list(combinations(range(n), r))
    # Explicit independent absence of higher rank on these toy instances.
    gr = list(combinations(range(n), r+1))
    assert all(minor(a, I, J) == 0 for I in gr for J in gr)
    I, J, d = next((I, J, t) for I in choices for J in choices
                   if (t := minor(a, I, J)))
    basis = []
    for k in sorted(set(range(n)) - set(J)):
        v = [0] * n
        v[k] = d
        for b, j in enumerate(J):
            newJ = J[:b] + (k,) + J[b+1:]
            v[j] = minor(a, I, newJ)
        assert all(reduce(xor, (mul(b, c) for b, c in zip(row, v)), 0) == 0 for row in a)
        basis.append(v)
    return basis


def residue_by_all_minors(basis, n):
    h = len(basis)
    a = list(zip(*basis))
    cols = tuple(range(h))
    o, rows = min((val(t), rows) for rows in combinations(range(n), h)
                  if (t := minor(a, rows, cols)))
    out = []
    for b in range(h):
        v = 0
        for i in range(n):
            z = minor(a, rows[:b] + (i,) + rows[b+1:], cols)
            assert not z or val(z) >= o
            if z and val(z) == o:
                v ^= 1 << i
        out.append(v)
    assert {sum(((v >> i) & 1) << j for j, i in enumerate(rows)) for v in out} == {1 << j for j in range(h)}
    return out


def expand(chart, x):
    return reduce(xor, (v for i, v in enumerate(chart) if (x >> i) & 1), 0)


def truth_eval(terms, x):
    return sum((x & m) == m for m in terms) & 1


def naive_anf_of_chart(terms, a, chart):
    out = []
    for u in range(1 << len(chart)):
        t = u
        c = 0
        while True:
            c ^= truth_eval(terms, a ^ expand(chart, t))
            if not t:
                break
            t = (t - 1) & u
        if c:
            out.append(u)
    return out


def basis_vectors(v, n):
    return [(v >> i) & 1 for i in range(n)]


def check_degree_criterion():
    tableaux = [
        (6, 3, [7, 25, 42], [[2, 12, 4, 10, 18, 8]], [[1, 0, 0, 0, 0, 0]], 4),
        (6, 4, [15], [[2, 4, 8, 16, 32, 64], [4, 2, 2, 16, 12, 8]],
         [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0]], 2),
        (6, 5, [31], [[2, 0, 0, 0, 8, 0], [0, 4, 0, 0, 0, 2], [0, 0, 8, 16, 0, 0]],
         [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]], 2)
    ]
    for n, j, terms, random_poly, coordinate_anchors, rank in tableaux:
        # For cubic n=6 nonzero anchors are in their own radical, reducing
        # alternating rank to <=4. The other tensors are single coordinate
        # volumes, whose contraction by j-2 anchors has rank <=2.
        kernel_by_cramer(contract(n, j, terms, coordinate_anchors), rank)
        a = contract(n, j, terms, random_poly)
        U = residue_by_all_minors(kernel_by_cramer(a, rank), n)
        for r in range(n):
            for args in combinations(U, j-1):
                z = poly_form(n, j, terms, [basis_vectors(v, n) for v in (1 << r,) + args])
                assert z == 0
        for offset in range(1 << n):
            restricted = naive_anf_of_chart(terms, offset, U)
            assert all(t.bit_count() < j for t in restricted)
        assert any(t.bit_count() == j for t in naive_anf_of_chart(terms, 0, [1 << i for i in range(n)]))
    print("independent direct minors: 3 maximal-rank polynomial examples; 192 affine offset checks lower degree")
    U = residue_by_all_minors([[2, 4, 0], [6, 28, 32]], 3)
    assert len(U) == 2 and all(U) and len(set(U)) == 2
    print("all-zero naive specialization loses a two-dimensional kernel basis; normalized residue preserves both pivots")


def check_affine_expansion():
    # Each test compares expanded ANF coefficients on an affine chart with
    # an independently computed sign-Walsh numerator at that chart.
    cases = [
        ([7, 30, 1], 13, [3, 5, 9, 17]),
        ([31, 28, 3, 0], 7, [17, 18, 20, 24]),
        ([7, 9, 18, 20], 17, [7, 19, 12]),
        ([15, 7, 3], 0, [13, 7, 3]),
    ]
    counts = 0
    for terms, offset, chart in cases:
        r = len(chart)
        assert len({expand(chart, x) for x in range(1 << r)}) == 1 << r
        coeff = set(naive_anf_of_chart(terms, offset, chart))
        vals = [(-1)**truth_eval(terms, offset ^ expand(chart, x)) for x in range(1 << r)]
        walsh = [sum(y*(-1)**((i & u).bit_count() & 1) for u, y in enumerate(vals)) for i in range(1 << r)]
        for S in range(1, 1 << r):
            w = sum(v for i, v in enumerate(walsh) if (i & S) == S)
            m = 1 << (r + 1 - S.bit_count())
            assert w % m == 0
            assert (w // m) % 2 == (S in coeff)
            counts += 1
    print(f"independent direct affine expansion vs Walsh divisibility: {counts} coefficients")
    # Repeated chart variable y1 appears twice in x0*x1 after restriction
    # x0=y1 and x1=y1: it contributes degree one, never degree two.
    assert naive_anf_of_chart([3], 0, [3, 4]) == [1]
    print("Boolean variable-merge negative control PASS")
    print("PASS: direct polarization, Cramer normalization, exhaustive cosets")


if __name__ == "__main__":
    check_degree_criterion()
    check_affine_expansion()
