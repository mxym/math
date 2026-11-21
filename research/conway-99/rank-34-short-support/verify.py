"""Exact Fourier identity and collision bounds, using the Python standard library."""
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import comb


def chi(n):
    return (0, 1, 1, -1, 1, -1, -1)[n % 7]


@cache
def bernoulli(k):
    if k == 0:
        return Fraction(1)
    return -sum(comb(k + 1, i) * bernoulli(i) for i in range(k)) / (k + 1)


@cache
def series(k, character_on_divisor):
    constant = 0
    if character_on_divisor:
        generalized = sum(chi(a) * comb(k, j) * bernoulli(j) *
                          Fraction(a, 7)**(k-j)
                          for a in range(1, 7) for j in range(k + 1))
        constant = -7**(k-1) * generalized / (2*k)
    return [constant] + [
        sum(d**(k-1) * chi(d if character_on_divisor else n//d)
            for d in range(1, n + 1) if n % d == 0)
        for n in range(1, 15)]


def multiply(a, b):
    return [sum(a[i] * b[n-i] for i in range(n+1)) for n in range(15)]


def verify_modular_relation():
    correction = (-13885354, -4954081, -1685907, -542542, -163198,
                  -45122, -11193)
    basis = {}
    for a, left, right in product(range(3, 12, 2), (False, True), (False, True)):
        b = 22 - a
        x = multiply(series(a, left), series(b, right))
        swap = multiply(series(a, not left), series(b, not right))
        power = 6 + (1 if left else -1)*((a-1)//2) + (1 if right else -1)*((b-1)//2)
        y = [Fraction(7)**power * coefficient for coefficient in swap]
        lhs = 2387*x[7] + 407*x[8] + 43*x[9] - x[11]
        rhs = sum(c*v for c, v in zip(correction, x)) + 81242*y[0]
        assert lhs == rhs + 22827*y[1] + 2737*y[2] + 196*y[3] + 7*y[4]
        row = list(map(Fraction, x))
        for i in range(15):
            if not row[i]:
                continue
            if i not in basis:
                basis[i] = [v/row[i] for v in row]
                break
            row = [v-row[i]*u for v, u in zip(row, basis[i])]
    assert len(basis) == 15
    assert correction[0] + 81242 == -13804112


def edge_histogram(n, k, adjacent):
    return Counter(sum(adjacent(u, v) for u, v in combinations(t, 2))
                   for t in combinations(range(n), k))


def verify_bounds():
    def prism(u, v):
        return u//3 == v//3 or u%3 == v%3

    triples = edge_histogram(6, 3, prism)
    equal_pairs = Counter()
    for i, ni in triples.items():
        for j, nj in triples.items():
            equal_pairs[18-2*(i+j)] += ni*nj
    assert (equal_pairs[6], equal_pairs[8]) == (4, 48)
    grid3 = edge_histogram(9, 3, prism)
    grid4 = edge_histogram(9, 4, prism)
    assert (grid3[2], grid3[1], grid4[5], grid4[4]) == (36, 36, 0, 45)
    weights = []
    for p in range(852):
        g, pairs = p//6, 5*p//2
        y3 = 24948 + max(0, 7392-2*p-4*pairs) + 2*(20790-9*p-36*g)
        y4 = 1398474 + (765072+18*p-48*pairs) + 2*(831600+36*p-2286*g)
        n14 = 2*((55440-5*(4158-3*p))//14)
        weighted = -13804112 + 2737*462 + 196*y3 + 7*y4 - 2387*n14
        weights.append(weighted)
        assert y3 >= 41058 and y4 >= 3156588
    assert min(weights) == 1439102 and weights[0] == 16920274
    assert 407*3534 < min(weights) <= 407*3536


if __name__ == "__main__":
    verify_modular_relation()
    verify_bounds()
    print("15-dimensional identity verified; N16 + N18 >= 3536 at rank 34")
