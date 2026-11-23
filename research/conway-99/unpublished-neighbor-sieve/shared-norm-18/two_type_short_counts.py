"""Verify the short-population identity and enumerate its integer consequences."""
from flint import fmpq_mat
from rank36_three_types import UNIT, short_equations


def check_identity():
    keys, rows = short_equations()
    allowed = {(0, 18), (0, 24)}
    keep = [i for i, k in enumerate(keys) if k not in UNIT - allowed]
    matrix = [[row[i] for i in keep] for row in rows]
    coeff = {(0, 0): 1080, (0, 14): 14, (1, 23): -9, (2, 22): -42, (2, 34): -1}
    assert set(coeff) <= {keys[i] for i in keep}
    target = [coeff.get(keys[i], 0) for i in keep]
    assert fmpq_mat(matrix).rank() == fmpq_mat([*matrix, target]).rank()


def check_populations():
    result = []
    for m in range(1, 189//42+1, 2):
        for b in range(0, 189//49+1, 2):
            for s in range(189//9+1):
                w34 = 189 - 42*m - 49*b - 9*s
                w18, rem = divmod(291 + 5*m + 16*b + 2*s, 6)
                if w34 >= 0 and rem == 0:
                    result.append((m, b, s, w18, w34))
    assert result == [
        (1, 0, 2, 50, 129), (1, 0, 5, 51, 102), (1, 0, 8, 52, 75),
        (1, 0, 11, 53, 48), (1, 0, 14, 54, 21),
        (1, 2, 1, 55, 40), (1, 2, 4, 56, 13),
        (3, 0, 0, 51, 63), (3, 0, 3, 52, 36), (3, 0, 6, 53, 9),
    ]


if __name__ == "__main__":
    check_identity()
    check_populations()
    print("Ten necessary short-population tuples. Each extension has one or three eligible 22-cocliques.")
