"""Exhaust the two rows of a nongrid support with zero binary image."""
from itertools import combinations, permutations


SUPPORTS = tuple(edge for edge in combinations(range(7), 2) for _ in range(2))


def eigenvector():
    values = []
    for j, (a, b) in enumerate(SUPPORTS):
        edge = {a, b}
        if edge == {0, 1}:
            value = 2
        elif edge in ({0, 3}, {1, 4}) and j % 2 == 0:
            value = -2
        elif 2 in edge:
            negative = bool(edge & {0, 1}) or (bool(edge & {5, 6}) and j % 2 == 0)
            value = -1 if negative else 1
        else:
            value = 0
        values.append(value)
    return values


def can_sign(rows):
    basis = {}

    def consistent(equation):
        while equation > 1:
            pivot = equation.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = equation
                return True
            equation ^= basis[pivot]
        return equation == 0

    def edge_sign(r, j):
        return 1 << (22 + 42*r + j)

    for r, row in enumerate(rows):
        for axis in range(7):
            equation, terms = 0, 0
            for j, edge in enumerate(SUPPORTS):
                if row[j] != 1 or axis not in edge:
                    continue
                terms += 1
                equation ^= edge_sign(r, j)
                if axis == edge[1]:
                    equation ^= (1 << (1 + j//2)) ^ (j % 2)
            if terms % 2 or not consistent(equation ^ (terms//2 % 2)):
                return False
    common = [j for j in range(42) if rows[0][j] == rows[1][j] == 1]
    assert len(common) == 2
    # Orthogonal signed roots at the common support require opposite products.
    equation = 1
    for j in common:
        equation ^= edge_sign(0, j) ^ edge_sign(1, j)
    return consistent(equation)


def verify():
    q = eigenvector()
    assert sum(v*v for v in q) == 28
    assert all(sum(q[j] for j, edge in enumerate(SUPPORTS) if a in edge) == 0
               for a in range(7))
    weights = [3*int(edge == (0, 1)) + 1 - len(set(edge) & {0, 1}) - q[j]
               for j, edge in enumerate(SUPPORTS)]
    light = [j for j, weight in enumerate(weights) if weight == 1]
    heavy = [j for j, weight in enumerate(weights) if weight == 2]
    assert len(light) == 16 and len(heavy) == 4
    checked = 0
    for double_u, double_v in permutations(heavy, 2):
        first = [0]*42
        first[double_u] = 2
        for j in heavy:
            if j not in (double_u, double_v):
                first[j] = 1
        for group in combinations(light, 8):
            for j in group:
                first[j] = 1
            degrees = [0]*7
            for (a, b), weight in zip(SUPPORTS, first):
                degrees[a] += weight
                degrees[b] += weight
            if degrees == [2, 2, 4, 4, 4, 4, 4]:
                second = [n - x for n, x in zip(weights, first)]
                assert sum(a*b for a, b in zip(first, second)) == 2
                checked += 1
                assert not can_sign((first, second))
            for j in group:
                first[j] = 0
    assert checked == 400
    print('400 ordered row pairs, 0 compatible sign systems.')


if __name__ == '__main__':
    verify()
