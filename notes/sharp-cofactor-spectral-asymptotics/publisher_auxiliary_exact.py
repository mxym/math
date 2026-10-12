"""Independent exact James-matrix check for the stage-summary local barrier.

Standard library only; Q(sqrt(3), i) arithmetic, no floating point.
The Kronecker quadratic form uses row-major vectorization.
"""
from fractions import Fraction
from itertools import permutations
import json

def scalar(a=0, b=0, c=0, d=0):
    return tuple(map(Fraction, (a, b, c, d)))

ZERO, ONE = scalar(), scalar(1)

def add(x, y):
    return tuple(a + b for a, b in zip(x, y))

def neg(x):
    return tuple(-a for a in x)

def sub(x, y):
    return add(x, neg(y))

def qmul(x, y):
    return (x[0] * y[0] + 3 * x[1] * y[1],
            x[0] * y[1] + x[1] * y[0])

def mul(x, y):
    rr, ii = qmul(x[:2], y[:2]), qmul(x[2:], y[2:])
    ri, ir = qmul(x[:2], y[2:]), qmul(x[2:], y[:2])
    return (rr[0] - ii[0], rr[1] - ii[1],
            ri[0] + ir[0], ri[1] + ir[1])

def conj(x):
    return (x[0], x[1], -x[2], -x[3])

def total(xs):
    result = ZERO
    for x in xs:
        result = add(result, x)
    return result

def product(xs):
    result = ONE
    for x in xs:
        result = mul(result, x)
    return result

def permanent(a):
    n = len(a)
    return total(product(a[i][p[i]] for i in range(n))
                 for p in permutations(range(n)))

def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))

def encoded(x):
    return list(map(str, x))

def main():
    r, i = scalar(0, 1), scalar(0, 0, 1)
    J = [[r, i, i, neg(i)],
         [neg(i), r, i, i],
         [neg(i), neg(i), r, neg(i)],
         [i, neg(i), i, r]]
    if any(J[a][b] != conj(J[b][a]) for a in range(4) for b in range(4)):
        raise ValueError("Not Hermitian")
    square = [[total(mul(J[a][k], J[k][b]) for k in range(4))
               for b in range(4)] for a in range(4)]
    if any(square[a][b] != mul(scalar(0, 2), J[a][b])
           for a in range(4) for b in range(4)):
        raise ValueError("Rank-two PSD polynomial identity failed")
    if total(J[a][a] for a in range(4)) != scalar(0, 4):
        raise ValueError("Wrong trace")
    if permanent(J) != scalar(24):
        raise ValueError("Wrong permanent")
    D = [[permanent([[J[x][y] for y in range(4) if y != b]
                     for x in range(4) if x != a])
          for b in range(4)] for a in range(4)]
    if any(D[a][b] != add(scalar(0, 4) if a == b else ZERO,
                          mul(scalar(2), conj(J[a][b])))
           for a in range(4) for b in range(4)):
        raise ValueError("Deleted-minor identity failed")
    V4 = [(0, 1, 2, 3), (1, 0, 3, 2),
          (2, 3, 0, 1), (3, 2, 1, 0)]
    t, omega = (1, 2, 0, 3), scalar(Fraction(-1, 2), 0, 0, Fraction(1, 2))
    powers = [ONE, omega, mul(omega, omega)]
    cosets = {}
    g = tuple(range(4))
    for exponent in range(3):
        for v in V4:
            p = compose(g, v)
            cosets[p] = exponent
        g = compose(t, g)
    if len(cosets) != 12:
        raise ValueError("Wrong A4 cosets")
    character_values = []
    for direction in [1, -1]:
        value = total(mul(powers[(direction * exponent) % 3],
                          product(J[a][p[a]] for a in range(4)))
                      for p, exponent in cosets.items())
        character_values.append(value)
    if scalar(24) not in character_values:
        raise ValueError("No equality character")
    # Row-major vec(E): coordinate (a,b) has index 4*a+b.
    # Coefficient of E_ab conjugate(E_cd) is D_ac D_db.
    # In conjugate(vec(E))^T M vec(E), M_(c,d),(a,b)
    # equals D^T_(c,a) D_(d,b): M = D^T tensor D.
    return {"status": "PASS", "arithmetic": "Q(sqrt(3),i), exact fractions",
            "James_hermitian": True, "James_square_equals_2sqrt3_times_J": True,
            "James_trace": "4sqrt(3)", "James_rank": 2,
            "James_permanent": "24",
            "all_16_deleted_minors_match_4sqrt3_I_plus_2_conjugate_J": True,
            "nonreal_A4_character_values": list(map(encoded, character_values)),
            "one_nonreal_character_equals_permanent": True,
            "deleted_minor_eigenvalues": ["4sqrt(3)", "8sqrt(3)"],
            "quadratic_vec_convention": "row-major; column-major uses D tensor D^T"}

if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
