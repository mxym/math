"""Independent exact certificate; Python standard library only."""
from fractions import Fraction as F
from itertools import permutations
import json
from pathlib import Path


def inversion(p):
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))


def perm_polynomial(A):
    coefficients = [F(0)] * (len(A) * (len(A) - 1) // 2 + 1)
    nonzero = []
    for p in permutations(range(len(A))):
        term = F(1)
        for i, j in enumerate(p):
            term *= A[i][j]
        if term:
            inv = inversion(p)
            coefficients[inv] += term
            nonzero.append({'one_line': [j + 1 for j in p], 'inversions': inv, 'coefficient': str(term)})
    return coefficients, nonzero


def determinant(A):
    value = F(0)
    for p in permutations(range(len(A))):
        term = F((-1) ** inversion(p))
        for i, j in enumerate(p):
            term *= A[i][j]
        value += term
    return value


def evaluate(coef, q):
    return sum(c * q ** k for k, c in enumerate(coef))


def derivative(coef, q):
    return sum(k * c * q ** (k - 1) for k, c in enumerate(coef) if k)


A = [[F(int(i == j)) for j in range(4)] for i in range(4)]
A[0][1] = A[1][0] = -F(99, 100)
A[0][3] = A[3][0] = F(1, 500)
A[1][3] = A[3][1] = F(1, 8)
coef, terms = perm_polynomial(A)
assert coef == [F(1), F(9801, 10000), F(0), F(1, 64), -F(99, 200000), F(1, 250000), F(0)]
minors = [determinant([row[:k] for row in A[:k]]) for k in range(1, 5)]
assert minors == [F(1), F(199, 10000), F(199, 10000), F(59, 15625)]
assert all(x > 0 for x in minors)
assert evaluate(coef, 49) == F(81807513, 500000)
assert evaluate(coef, 50) == F(7969, 50)
assert evaluate(coef, 49) - evaluate(coef, 50) == F(2117513, 500000) > 0
assert derivative(coef, 50) == -F(10831, 2500) < 0

# Check the spaced-triangle formula independently at several dimensions,
# enumerating n! permutations. This is only a sanity check on the general proof.
spacing_checks = []
for n in range(4, 9):
    a, b, c = -F(3, 5), F(1, 7), F(1, 9)
    B = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    B[0][1] = B[1][0] = a
    B[0][-1] = B[-1][0] = b
    B[1][-1] = B[-1][1] = c
    co, _ = perm_polynomial(B)
    m = 2 * n - 5
    expected = [F(0)] * len(co)
    expected[0], expected[1], expected[m], expected[m + 1], expected[m + 2] = F(1), a*a, c*c, 2*a*b*c, b*b
    assert co == expected
    spacing_checks.append(n)

result = {'result': 'PASS', 'matrix': [[str(v) for v in row] for row in A],
          'polynomial_coefficients': [str(v) for v in coef], 'nonzero_permutations': terms,
          'leading_minors': [str(v) for v in minors], 'P49': str(evaluate(coef, 49)),
          'P50': str(evaluate(coef, 50)), 'P49_minus_P50': str(evaluate(coef,49)-evaluate(coef,50)),
          'derivative_at_50': str(derivative(coef, 50)), 'spacing_formula_checked_orders': spacing_checks,
          'meaning': 'Exact rational arithmetic verification; not Lean or peer review.'}
print(json.dumps(result, indent=2))
Path(__file__).with_name('EXACT_CERTIFICATE.json').write_text(json.dumps(result, indent=2)+'\n')
