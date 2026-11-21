from fractions import Fraction as F
from itertools import product


def check(flag, msg):
    if not flag:
        raise ArithmeticError(msg)


SIG = (F(".10"), F(".14"))
THETA = F(7, 32)
EPS = F("0.0001")
B_CUT = F(".090")
ROWS = [
    ((".073", ".089"), (".187", ".205"), (".242", ".252"), False),
    ((".070", ".089"), (".232", ".247"), (".201", ".205"), True),
]
OLD = F(".20")

count = 0
for j, (A, B, E, swap) in enumerate(ROWS, 1):
    A, B, E = (tuple(map(F, pair)) for pair in (A, B, E))
    check(A[1] < B_CUT and 3 * B_CUT > B[1], "unique small part/rank")
    check(A[0] + B[0] > OLD and E[0] > OLD, "literal original remainder")
    check(A[0] + B[0] + E[0] > F(".5"), "strictly super-half")
    check(B[1] < E[0] if not swap else
          B[0] > E[1] and B[1] - E[0] < B_CUT,
          "B and true Lambda prime are coprime")
    maxes = [F(0)] * 3
    for sigma, a, b, ell in product(SIG, A, B, E):
        q1, q2, q3 = (a, ell, b) if swap else (a, b, ell)
        l2 = 2 * sigma + q2 + 2 * q3
        l3 = THETA + sigma + q1 + 5 * q2 + 2 * q3
        l4 = 2 * THETA * (sigma + q3 - q2) + sigma + q1 + 5 * q2 + 2 * q3
        check(q1 < sigma - EPS and l2 < 1 - 8 * EPS and
              max(l3, l4) < 2 - 15 * EPS, ("Prop 5.2", j, sigma, a, b, ell))
        maxes = list(map(max, maxes, [l2, l3, l4]))
        count += 1
    print("row", j, "log_x modulus", A[0] + B[0] + E[0], A[1] + B[1] + E[1],
          "exact rail maxima", *maxes)
check(F(ROWS[1][2][1]) < F(ROWS[0][2][0]), "actual Lambda slots disjoint")
for p in range(2, 1000):
    check(1 + F(1, p - 1) / p - F(p, p - 1) / p**2 == 1, ("harmonic Euler", p))
print(count, "vertex tests; 998 exact local harmonic identities passed")
