"""Replay the eleven edge-complement discriminant calculations with python-flint."""
from itertools import combinations, product
from math import lcm, prod

from flint import fmpz, fmpz_mat as Matrix


def block_sum(*blocks):
    size = sum(block.nrows() for block in blocks)
    result = Matrix(size, size)
    offset = 0
    for block in blocks:
        for i in range(block.nrows()):
            for j in range(block.ncols()):
                result[offset + i, offset + j] = block[i, j]
        offset += block.nrows()
    return result


def binary(a, b, c):
    return Matrix([[a, b], [b, c]])


B7 = binary(2, 1, 4)
J = block_sum(B7, B7)
A4 = Matrix([[2 if i == j else -int(abs(i-j) == 1) for j in range(4)] for i in range(4)])
K196 = block_sum(Matrix([[4]]), B7, B7)
K180 = block_sum(Matrix([[4]]), binary(2, 1, 2), binary(4, 1, 4))
CASES = {
    (1,1,1,1,1,1): (K196, 196, 60),
    (2,1,1,1,1): (K180, 180, 420),
    (2,2,1,1): (K196, 196, 420),
    (2,2,2): (K180, 180, 420),
    (3,1,1,1): (block_sum(Matrix([[4]]), B7, binary(30,15,60)), 44100, 60),
    (3,2,1): (block_sum(Matrix([[4]]), A4), 20, 420),
    (3,3): (K196, 196, 60),
    (4,1,1): (block_sum(Matrix([[4]]), binary(2,1,8), binary(94,47,94)), 397620, 19740),
    (4,2): (block_sum(Matrix([[4]]), B7, binary(470,235,940)), 10824100, 19740),
    (5,1): (K196, 196, 27060),
    (6,): (block_sum(Matrix([[20]]), binary(2,1,12), binary(2,1,12)), 10580, 19320),
}


def edge_shell(parts):
    adjacency = Matrix(27, 27)

    def join(i, j):
        adjacency[i, j] = adjacency[j, i] = 1

    for i, j in combinations(range(3), 2):
        join(i, j)
    for i in range(12):
        join(0, 3+i)
        join(1, 15+i)
        join(3+i, 15+i)
    offset = 0
    for part in parts:
        for j in range(part):
            join(3+offset+2*j, 3+offset+2*j+1)
            join(15+offset+2*j+1, 15+offset+(2*j+2)%(2*part))
        offset += 2*part
    assert offset == 12
    return adjacency


def shell_basis(adjacency):
    # Nine times the centered shell Gram, including the two dependent columns.
    full = Matrix([[27*int(i == j) - 9*adjacency[i,j] + 1 for j in range(27)]
                   for i in range(27)])
    ids = [1, 2, *range(3,14), *range(15,26)]
    basis = Matrix(27, 25)
    basis[0,0] = 3
    for k, i in enumerate(ids, start=1):
        basis[i,k], basis[0,k] = 1, -1
    gram = (basis.transpose()*full*basis)/9
    pairings = basis.transpose()*full
    assert pairings.transpose()*gram.inv()*pairings == 9*full
    for vertex in (0, 1):
        relation = Matrix([[4*int(i == vertex)+adjacency[i,vertex]] for i in range(27)])
        assert (full*relation).is_zero()
    for n in range(1, 26):
        assert Matrix([[gram[i,j] for j in range(n)] for i in range(n)]).det() > 0
    return gram


def kernel_mod(rows, p):
    reduced = [[entry%p for entry in row] for row in rows]
    pivots = []
    for j in range(len(rows)):
        k = len(pivots)
        pivot = next((i for i in range(k, len(rows)) if reduced[i][j]), None)
        if pivot is None:
            continue
        reduced[k], reduced[pivot] = reduced[pivot], reduced[k]
        inverse = pow(reduced[k][j], -1, p)
        reduced[k] = [x*inverse%p for x in reduced[k]]
        for i, row in enumerate(reduced):
            if i != k and row[j]:
                factor = row[j]
                reduced[i] = [(a-factor*b)%p for a,b in zip(row, reduced[k])]
        pivots.append(j)
    free = [j for j in range(len(rows)) if j not in pivots]
    kernel = []
    for j in free:
        vector = [0]*len(rows)
        vector[j] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -reduced[i][j]%p
        kernel.append(vector)
    return kernel


def extension_vector(gram, p):
    size = gram.nrows()
    kernel = kernel_mod([[int(gram[i,j]) for j in range(size)] for i in range(size)], p)
    if not kernel:
        return None
    rows = Matrix(kernel)
    form = rows*gram*rows.transpose()
    modulus = 2*p*p
    # Three coordinates suffice for finding a line at odd p. A negative
    # answer below is accepted only when all projective lines were examined.
    cap = len(kernel) if p == 2 else min(3, len(kernel))
    for length in range(1, cap+1):
        for indices in combinations(range(len(kernel)), length):
            for tail in product(range(1,p), repeat=length-1):
                coefficients = list(zip(indices, (1,*tail)))
                norm = sum(a*b*int(form[i,j]) for i,a in coefficients for j,b in coefficients)
                if norm % modulus:
                    continue
                vector = [sum(a*kernel[i][j] for i,a in coefficients)%p for j in range(size)]
                pivot = next(j for j,v in enumerate(vector) if v)
                unit = pow(vector[pivot], -1, p)
                return pivot, [v*unit%p for v in vector]
    assert len(kernel) <= cap
    return None


def maximal_extension(gram):
    gram = Matrix(gram)
    for prime, _ in abs(gram.det()).factor():
        p = int(prime)
        while (line := extension_vector(gram, p)) is not None:
            pivot, vector = line
            column = Matrix([[v] for v in vector])
            pairings = gram*column
            norm = int((column.transpose()*pairings)[0,0])
            assert vector[pivot] == 1 and all(x%p == 0 for x in pairings.entries())
            assert norm%(2*p*p) == 0
            determinant = gram.det()
            for i in range(gram.nrows()):
                gram[i,pivot] = gram[pivot,i] = pairings[i,0]//p
            gram[pivot,pivot] = norm//(p*p)
            assert gram.det()*p*p == determinant
    return gram


def main():
    for partition, (auxiliary, determinant, expected_scale) in CASES.items():
        gram = shell_basis(edge_shell(partition))
        inverse = gram.inv()
        level = lcm(*(int(x.denom()) for x in inverse.entries()),
                    *(int((inverse[i,i]/2).denom()) for i in range(25)))
        scale = prod(int(p)**((e+1)//2) for p,e in fmpz(level).factor())
        assert scale == expected_scale and auxiliary.det() == determinant
        remainder = maximal_extension(block_sum(J, -gram))
        assert abs(remainder.det()) == determinant
        assert maximal_extension(auxiliary).det() == determinant
        assert abs(maximal_extension(block_sum(remainder, auxiliary)).det()) == 1
        print(partition, 'det', determinant, 'scale', scale, flush=True)


if __name__ == '__main__':
    main()
