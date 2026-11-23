"""Exact residue count and dimension check for the two-type hypothesis."""
from collections import Counter
from functools import cache
from math import gcd

from flint import fmpq_mat
from higher_moments import DUAL7, GRAM, SHIFTS, dot, projections, rows, times
from rank36_three_types import UNIT

project = cache(projections)
SHIFTS_USED = (None, *SHIFTS)
AXES = ((1, 2, 3, 1), (1, -1, 1, -2), (1, 0, 0, 0))
# Raw shells absent on the two-type face. Raw (1,27) retains 9 times (0,18).
ABSENT = UNIT - {(0, 18), (0, 24)}
RAW_ZEROS = ABSENT - {(1, 27)}
TRANSFERS = (((1, 25), (0, 16), 8), ((1, 27), (0, 18), 9),
             ((1, 27), (2, 26), 2), ((0, 26), (1, 21), 8))


def norm7(a, t):
    return (t - 4*11*a*a) % 7


def check_residue_count():
    # A plane basis with Gram 4I and distinguished vector (1,0).
    plane = [(i, j) for i in range(7) for j in range(7)]
    multiplicity = Counter((4*(i*i+j*j) % 7, 4*i % 7) for i, j in plane)
    raw = rows()
    types = sorted(set().union(*raw, *(project(sh, n) for sh in SHIFTS_USED for n in (1, 2))))
    atoms, by = {}, {}
    for a, t in types:
        by[a, t] = []
        if (a, t) in RAW_ZEROS:
            continue
        for i in range(7):
            ways = multiplicity[norm7(a, t), i]
            if ways:
                key = (a, t, min(i, (-i) % 7) if a == 0 else i)
                index = atoms.setdefault(key, len(atoms))
                by[a, t].append((i, index, ways))
    ncols = len(atoms)
    equations = []

    def add(row, constant=0):
        row = [*row, constant]
        div = gcd(*row)
        if div:
            equations.append(tuple(x//div for x in row))

    def folded(coefficients):
        # Eight times the usual mean over all anti-isometries.
        result = [0]*ncols
        for (a, t), value in coefficients.items():
            factor = 1 if norm7(a, t) else 8
            for _, j, _ in by[a, t]:
                result[j] += factor*value
        return result

    for original in [*raw, *[{k: 1} for k in sorted(ABSENT)]]:
        coeff = dict(original)
        for target, source, count in TRANSFERS:
            coeff[source] = coeff.get(source, 0) - count*original.get(target, 0)
        add(folded(coeff))
    add(folded({(0, 0): 1}), -8)

    images = [(i, 0, j, 0) for i, j in plane if 4*(i*i+j*j) % 7 == (-18) % 7]
    assert len(images) == 8
    for shift in SHIFTS_USED:
        scale = 1 if shift is None else 3
        for image in images:
            pairing = times(DUAL7, image)
            for h in AXES:
                axis_norm = 9*dot(h, times(GRAM, h))
                shells = []
                for n in (1, 2):
                    angles = [0]*ncols
                    for (a, t), numerators in project(shift, n).items():
                        contribution = Counter()
                        for w in numerators:
                            i = -dot(pairing, w)*pow(scale, -1, 7) % 7
                            ip = (3//scale)*dot(w, h)
                            contribution[i] += 48*ip*ip - 2*n*axis_norm
                        for i, j, ways in by[a, t]:
                            angles[j] += (2//ways)*(1+(a != 0))*contribution[i]
                    shells.append(angles)
                add([b+48*a for a, b in zip(*shells)])

    # Twice the stated homogeneous identity, including the affine constant.
    target = [-x for x in folded({(1, 23): 1})] + [-2*792]
    for (a, t, i), weight in (
        ((0, 18, 4), 72), ((0, 14, 0), -20), ((0, 22, 3), -12),
        ((1, 29, 1), -1), ((2, 22, 0), -22), ((3, 33, 0), -12),
        ((3, 35, 1), -12),
    ):
        j, = [j for residue, j, _ in by[a, t] if residue == i]
        target[j] += 2*weight
    rank = fmpq_mat(equations).rank()
    assert fmpq_mat([*equations, target]).rank() == rank
    assert multiplicity[18 % 7, 18 % 7] == 1


def affine_dimension(count):
    return (24*(count-1) + count+23)//(count+24)


def check_dimension():
    # Sorted class sizes after deletion and optional trimming to 180 lines.
    minimum = 100
    for a in range(3, 46):
        for b in range(a, (180-a)//3+1):
            for c in range(b, (180-a-b)//2+1):
                counts = (a, b, c, 180-a-b-c)
                if sum(max(0, 17-x) for x in counts) <= 14:
                    minimum = min(minimum, sum(map(affine_dimension, counts)))
    assert minimum == 43
    assert sum(map(affine_dimension, (3, 17, 17, 143))) == minimum
    directions = ((1, 0), (0, 1), (2, 2), (2, -2))
    assert all(4*dot(v, v) % 7 == 4 for v in directions)
    assert {4*dot(v, w) % 7 for i, v in enumerate(directions)
            for w in directions[:i]} == {0, 1, 6}


if __name__ == "__main__":
    check_residue_count()
    check_dimension()
    print("At least 17 per signed residue. After 14 deletions the required dimension is at least 43+2.")
