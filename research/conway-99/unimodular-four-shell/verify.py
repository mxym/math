"""Replay the four-dimensional projection and the mod-two obstruction."""

from itertools import permutations, product


def det(matrix):
    result = 0
    for p in permutations(range(len(matrix))):
        inversions = sum(i < j and p[i] > p[j] for i in range(len(p)) for j in range(len(p)))
        term = (-1) ** inversions
        for i, j in enumerate(p):
            term *= matrix[i][j]
        result += term
    return result


def dot(x, y):
    return sum(2*x[i]*y[i] + x[i]*y[i+1] + x[i+1]*y[i] + 4*x[i+1]*y[i+1]
               for i in (0, 2))


def main():
    basis = [(-1, 1, 0, 0), (-1, 0, 1, 0), (0, 0, -1, 1), (1, 1, 1, 0)]
    e = (0, 1, 0, 1)
    gram = [[dot(x, y) for y in basis] for x in basis]
    assert abs(det(basis)) == 3
    assert gram == [[4, 1, 0, 2], [1, 4, -1, -1], [0, -1, 4, -1], [2, -1, -1, 10]]
    assert det(gram) == 441 and dot(e, e) == 8
    assert [dot(x, e) for x in basis] == [3, 0, 3, 6]
    avoiding = [h for h in product(range(2), repeat=4)
                if all(dot(h, x) % 2 for x in [e, *basis[:3]])]
    assert len(avoiding) == 2
    assert all(dot(h, h) % 4 == 2 for h in avoiding)
    print("Projection Gram matrix:", gram)
    print("Required pairings: 1, 0, 1, 2. Index 3, determinant 441.")
    print("Both mod-two classes avoiding all four tests are anisotropic.")


if __name__ == "__main__":
    main()
