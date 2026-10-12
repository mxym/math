#!/usr/bin/env python3
"""Exact regression checks for the robust rank-decomposition cofactor formula.

This checks the determinant signs and normalizations in the signed cofactor lemma in paper.md.
It does not replace the proof. Uses only the Python standard library, and
all checks remain active under ``python -O``.
"""

from fractions import Fraction
from random import Random


def determinant(matrix):
    """Compute a square determinant by exact rational elimination."""
    size = len(matrix)
    work = [[Fraction(value) for value in row] for row in matrix]
    result = Fraction(1)
    for pivot_column in range(size):
        pivot_row = next(
            (row for row in range(pivot_column, size) if work[row][pivot_column]),
            None,
        )
        if pivot_row is None:
            return Fraction(0)
        if pivot_row != pivot_column:
            work[pivot_column], work[pivot_row] = (
                work[pivot_row],
                work[pivot_column],
            )
            result = -result
        pivot = work[pivot_column][pivot_column]
        result *= pivot
        for column in range(pivot_column, size):
            work[pivot_column][column] /= pivot
        for row in range(pivot_column + 1, size):
            multiplier = work[row][pivot_column]
            for column in range(pivot_column, size):
                work[row][column] -= multiplier * work[pivot_column][column]
    return result


def column_determinant(columns):
    return determinant([list(row) for row in zip(*columns)])


def main():
    random = Random(541)
    checks = 0
    for dimension in range(3, 8):
        for trial in range(30):
            while True:
                basis = [
                    [Fraction(random.randint(-5, 5), 7) for _ in range(dimension)]
                    for _ in range(dimension)
                ]
                basis_determinant = column_determinant(basis)
                if basis_determinant:
                    break
            alpha = [
                Fraction(random.randint(-5, 5), 7) for _ in range(dimension)
            ]
            beta = [
                Fraction(random.randint(-5, 5), 7) for _ in range(dimension)
            ]
            x = [
                sum(alpha[index] * basis[index][row] for index in range(dimension))
                for row in range(dimension)
            ]
            y = [
                sum(beta[index] * basis[index][row] for index in range(dimension))
                for row in range(dimension)
            ]
            for omitted in range(dimension):
                remaining = [index for index in range(dimension) if index != omitted]
                columns = [basis[index] for index in remaining] + [x, y]
                cofactors = [
                    (-1) ** index
                    * column_determinant(columns[:index] + columns[index + 1 :])
                    for index in range(dimension + 1)
                ]
                relation = [
                    alpha[omitted] * beta[index] - beta[omitted] * alpha[index]
                    for index in remaining
                ] + [beta[omitted], -alpha[omitted]]
                factor = (-1) ** omitted * basis_determinant
                expected = [factor * coefficient for coefficient in relation]
                if cofactors != expected:
                    raise RuntimeError(
                        "Signed cofactor identity failed: "
                        f"dimension={dimension}, trial={trial}, omitted={omitted}, "
                        f"actual={cofactors}, expected={expected}"
                    )
                residual = [
                    sum(
                        cofactors[index] * columns[index][row]
                        for index in range(dimension + 1)
                    )
                    for row in range(dimension)
                ]
                if any(residual):
                    raise RuntimeError(
                        "Cofactor relation failed to annihilate tuple: "
                        f"dimension={dimension}, trial={trial}, omitted={omitted}, "
                        f"residual={residual}"
                    )
                checks += 1
    if checks != 750:
        raise RuntimeError(f"Unexpected check count: {checks}; expected 750")
    print(
        f"Exact Fraction audit passed: {checks} omitted-index cofactor identities "
        "in dimensions 3 through 7 (seed 541)."
    )


if __name__ == "__main__":
    main()
