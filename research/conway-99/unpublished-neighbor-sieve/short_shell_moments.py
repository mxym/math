"""Exact second moments of the rank-48 gluings, and the small-support test."""
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, product
from math import ceil
from fractions import Fraction

from flint import fmpq_mat


GRAM = ((2, 1, 0, 0), (1, 4, 0, 0), (0, 0, 2, 1), (0, 0, 1, 4))
DUAL7 = ((4, -1, 0, 0), (-1, 2, 0, 0), (0, 0, 4, -1), (0, 0, -1, 2))
SHIFTS = ((-2, 0, 0, 0), (-2, 1, 0, 0), (-1, 1, -1, 1))
PAIRS = list(combinations_with_replacement(range(4), 2))
FAMILIES = (
    ((0, 24), (1, 25), (2, 28)),
    ((0, 20), (1, 21), (1, 27), (2, 30)),
    ((0, 16), (0, 18), (0, 26), (3, 37)),
)
# Coefficients of a zero linear combination of the folded shell populations.
TOTAL_ROW = {
    (0, 0): -131246, (0, 14): -2873, (0, 16): -1284, (0, 18): 2056,
    (0, 20): 2056, (0, 24): 1250, (0, 26): 584, (1, 21): 2056,
    (1, 23): -2366, (1, 25): 2056, (1, 27): 532, (2, 26): -1064,
    (2, 28): -22, (2, 30): 976, (3, 33): -1456, (3, 35): -1978,
    (3, 37): 144, (4, 44): -1874, (4, 46): -135,
}


def dot(x, y):
    return sum(i*j for i, j in zip(x, y))


def times(matrix, x):
    return tuple(dot(row, x) for row in matrix)


def possible(a, t):
    return (t >= 11*a and (t-11*a) % 2 == 0
            and not (a == 0 and 0 < t < 14)
            and not (a == 1 and t <= 19)
            and (a, t) != (2, 24))


def moment_rows(shift):
    table = defaultdict(lambda: [0]*len(PAIRS))

    def add(key, g, multiplicity):
        for j, (u, v) in enumerate(PAIRS):
            table[key][j] += multiplicity*(2*g[u]*g[v] - GRAM[u][v]*g[0]**2)

    if shift is None:
        for w in product(range(-2, 3), range(-4, 5), range(-2, 3), range(-4, 5)):
            n = dot(w, times(DUAL7, w))
            if n > 28:
                continue
            for a in (0, 3):
                t = 28 - n + 11*a*a//9
                if possible(a, t):
                    add((a, t), w, 2 if a else 1)
        scale = 1
    else:
        e = times(GRAM, shift)
        assert dot(e, shift) == 8
        for j in (-1, 0, 1):
            bounds = (8, 12, 8, 12)
            choices = [range(-b + (b+j*v) % 3, b+1, 3) for b, v in zip(bounds, e)]
            for g in product(*choices):
                n = dot(g, times(DUAL7, g))
                if n > 252:
                    continue
                a = (-dot(shift, g)+4) % 9 - 4
                t, rem = divmod(252-n+11*a*a, 9)
                if a >= 0 and rem == 0 and possible(a, t):
                    add((a, t), g, 2 if a else 1)
        scale = 3
    # The roots in the 44-space contribute zero to these polynomials.
    for i in (0, 2):
        if shift is None or dot(GRAM[i], shift) % 3 == 0:
            add((0, 0), [scale*v for v in GRAM[i]], 2*48)
    return [{k: counts[j] for k, counts in table.items() if counts[j]}
            for j in range(len(PAIRS))]


def columns(matrix, indices):
    return fmpq_mat([[matrix[r, j] for j in indices] for r in range(matrix.nrows())])


def nonnegative_solution(matrix, target):
    # A feasible cone contains the target in a cone on linearly independent columns.
    rank = matrix.rank()
    if rank != fmpq_mat([row + [target[i, 0]] for i, row in enumerate(matrix.tolist())]).rank():
        return False
    reduced, _ = matrix.transpose().rref()
    rows = [next(j for j in range(reduced.ncols()) if reduced[i, j]) for i in range(rank)]
    m = fmpq_mat([[matrix[i, j] for j in range(matrix.ncols())] for i in rows])
    b = fmpq_mat([[target[i, 0]] for i in rows])
    for indices in combinations(range(matrix.ncols()), rank):
        basis = columns(m, indices)
        if not basis.det():
            continue
        x = basis.solve(b)
        if all(x[i, 0] >= 0 for i in range(rank)):
            return True
    return False


def four_types(keys, independent):
    nonzero = [k for k in keys if (9*k[1]-11*k[0]**2) % 7]
    assert len(nonzero) == 18
    coeff = {k: [int(row[keys.index(k)]) for row in independent] for k in keys}
    # Coordinates are W(0,14), W(1,23)-99, W(2,22), W(4,46), four allowed
    # nonisotropic populations, and 8-W(0,14). All are nonnegative.
    target = fmpq_mat([[-x-99*y] for x, y in zip(coeff[0, 0], coeff[1, 23])] + [[8]])
    def feasible(choices):
        selected = [(0, 14), (1, 23), (2, 22), (4, 46), *choices]
        mat = fmpq_mat([[coeff[k][i] for k in selected] + [0] for i in range(len(independent))]
                       + [[int(k == (0, 14)) for k in selected] + [1]])
        return nonnegative_solution(mat, target)

    assert not any(feasible(four) for four in combinations(nonzero, 4))
    # The same equations really do admit nonnegative rational populations.
    assert feasible(((0, 16), (0, 18), (0, 26), (1, 25), (1, 27)))


def two_unit_types(keys, independent):
    # Change coordinates from whole shells to their signed-unit populations.
    # Each remaining vector is counted by one of the four translations below.
    rows = [list(row) for row in independent]
    for target, source, multiplicity in (
        ((1, 25), (0, 16), 8), ((1, 27), (0, 18), 9),
        ((1, 27), (2, 26), 2), ((0, 26), (1, 21), 8),
    ):
        for row in rows:
            row[keys.index(source)] += multiplicity*row[keys.index(target)]
    types = sorted({k for group in FAMILIES for k in group} | {(2, 26)})
    always = [k for k in keys if k not in types and k != (0, 0)]
    target = fmpq_mat([[-row[keys.index((0, 0))]-99*row[keys.index((1, 23))]]
                       for row in rows] + [[8]])
    allowed = []
    for pair in combinations(types, 2):
        keep = always + list(pair)
        mat = fmpq_mat([[row[keys.index(k)] for k in keep] + [0] for row in rows]
                       + [[int(k == (0, 14)) for k in keep] + [1]])
        if nonnegative_solution(mat, target):
            allowed.append(pair)
    assert allowed == [((0, 16), (0, 18)), ((0, 18), (0, 24)), ((0, 18), (1, 25))]
    # A singleton extends to eleven different pairs, so it cannot be feasible.
    print('Unit-labeling test: 63 of 66 pairs excluded; each survivor contains (0,18).')


def norm_eighteen_bound():
    energies = ((Fraction(1421, 108), Fraction(1085, 92)),
                (Fraction(1337, 108), Fraction(231, 20)),
                (Fraction(1421, 108), Fraction(553, 44)),
                (Fraction(161, 12), Fraction(161, 12)))
    caps = [[int(16/(2*d-20)) for d in row] for row in energies]
    seed = (sum(r[0]*w for r, w in zip(caps, (12, 3, 6, 1))),
            sum(r[1]*w for r, w in zip(caps, (7, 2, 2, 0))),
            sum(r[1]*w for r, w in zip(caps, (8, 1, 2, 0))))
    assert seed == (47, 44, 43)
    assert 99*560*max(seed)//9 == 289520


def rank_42_rooted_bound():
    plane_shell = [v for v in product(range(7), repeat=2) if dot(v, v) % 7 == 4]
    assert len(plane_shell) == 8
    for differences, expected in [((16, 18, 20, 22), 4), ((18, 20, 22), 3), ((18, 22), 2)]:
        residues = {(18 - delta//2) % 7 for delta in differences}
        assert 4 not in residues
        largest = max(len(group) for k in range(9) for group in combinations(plane_shell, k)
                      if all(dot(x, y) % 7 in residues for x, y in combinations(group, 2)))
        assert largest == expected
        print('Rank 42, allowed squared differences', differences, 'N18 <=', 99*560*largest//9)


def main():
    tables = [moment_rows(e) for e in (*SHIFTS, None)]
    rows = sum(tables, [])
    keys = sorted({k for row in rows for k in row})
    basis = fmpq_mat([[row.get(k, 0) for k in keys] for row in rows])
    assert len(keys) == 23 and basis.rank() == 7
    # The three certificates each use only one harmonic polynomial.
    for family, (table, j, scale), bound in zip(
        FAMILIES, ((1, 7, 72), (2, 2, -4), (3, 4, 4)),
        (Fraction(49), Fraction(21, 4), Fraction(329, 16)),
    ):
        row = {k: Fraction(v, scale) for k, v in tables[table][j].items()}
        positive = {k for k, v in row.items() if k not in ((0, 0), (1, 23)) and v > 0}
        assert positive == set(family) and row.get((1, 23), 0) <= 0
        assert (-row.get((0, 0), 0)-99*row.get((1, 23), 0))/max(row[k] for k in positive) == bound
    total = fmpq_mat([[TOTAL_ROW.get(k, 0) for k in keys]])
    assert fmpq_mat(basis.tolist() + total.tolist()).rank() == basis.rank()
    assert all(v <= 2056*int(any(k in group for group in FAMILIES))
               for k, v in TOTAL_ROW.items() if k not in ((0, 0), (1, 23)))
    lower = Fraction(131246+99*2366, 2056)
    print('Minimum populations at ranks 36, 38, 40, 42:',
          [ceil(lower*(7**m+1)) for m in (4, 3, 2, 1)])
    echelon, rank = basis.transpose().rref()
    indices = [next(j for j in range(echelon.ncols()) if echelon[i, j]) for i in range(rank)]
    independent = [[basis[i, j] for j in range(len(keys))] for i in indices]
    four_types(keys, independent)
    print('Seven independent moment equations. All 3,060 four-type choices excluded.')
    two_unit_types(keys, independent)
    norm_eighteen_bound()
    rank_42_rooted_bound()


if __name__ == '__main__':
    main()
