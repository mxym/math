#!/usr/bin/env python3
"""Exact finite checks for cq-quotient-shannon-face.md; standard library only."""

from fractions import Fraction as Q
from itertools import product


def subgroup_checks(moduli):
    G = tuple(product(*(range(m) for m in moduli)))
    zero = (0,) * len(moduli)
    def plus(a, b):
        return tuple((x + y) % m for x, y, m in zip(a, b, moduli))
    subgroups = []
    for mask in range(1 << (len(G) - 1)):
        H = {zero} | {g for j, g in enumerate(G[1:]) if mask & (1 << j)}
        if all(plus(h, k) in H for h, k in product(H, repeat=2)):
            subgroups.append(H)
    checks = 0
    for J, K in product(subgroups, repeat=2):
        meet, join = J & K, {plus(j, k) for j, k in product(J, K)}
        assert len(meet) * len(join) == len(J) * len(K)
        labels = {g: [min(plus(g, h) for h in H) for H in (J, K, meet, join)] for g in G}
        for x, y in product(G, repeat=2):
            u, v, t, w = [a == b for a, b in zip(labels[x], labels[y])]
            assert t == (u and v)
            assert w or not (u or v)
            checks += 1
    return len(subgroups), checks


def deficit(z, order):
    # log 2 - h(sqrt(z)) is the sum z^j/((2j)(2j-1)).
    lower = sum((z ** j / (2*j*(2*j-1)) for j in range(1, order + 1)), Q())
    return lower, lower + z ** (order + 1) / (
        (1 - z) * (2*order + 2) * (2*order + 1)
    )


def entropy_example():
    a = Q(1, 2)
    lo, hi = map(Q, ("19/40", "12/25"))
    alo, ahi = deficit(a*a, 28)
    lo0, lo1 = deficit(a*a + lo*lo, 28)
    hi0, hi1 = deficit(a*a + hi*hi, 28)
    assert lo0 < lo1 < 2*alo <= 2*ahi < hi0 < hi1
    # Positive definiteness and strict covariance determinant on the root bracket.
    assert a*a + hi*hi < 1
    assert (1 - a*a - hi*hi)*lo*lo > 0


def scale(k, A):
    return tuple(tuple(k*x for x in row) for row in A)


def add(A, B):
    return tuple(tuple(x+y for x, y in zip(u, v)) for u, v in zip(A, B))


def mul(A, B):
    return tuple(tuple(sum(x*y for x, y in zip(u, v)) for v in zip(*B)) for u in A)


def tr(A):
    return sum(A[j][j] for j in range(len(A)))


def kron(A, B):
    return tuple(tuple(a*b for a in u for b in v) for u in A for v in B)


def tensor(xs):
    P = ((1,),)
    for x in xs:
        P = kron(P, x)
    return P


def pauli_and_tensor():
    I, X, Z = ((1, 0), (0, 1)), ((0, 1), (1, 0)), ((1, 0), (0, -1))
    a, b = Q(1, 2), Q(19, 40)
    B = add(scale(a, Z), scale(b, X))
    rho = scale(Q(1, 2), add(I, B))
    C = add(mul(Z, B), scale(-1, mul(B, Z)))
    v = a*a + b*b
    assert tr(mul(rho, C)) == 0
    var1 = tr(mul(rho, mul(Z, Z))) - a*a
    var2 = tr(mul(rho, mul(B, B))) - v*v
    cov = tr(mul(rho, scale(Q(1, 2), add(mul(Z, B), mul(B, Z))))) - a*v
    assert (var1, var2, cov) == (1 - a*a, v*(1-v), a*(1-v))
    assert var1*var2 - cov*cov == b*b*(1-v) > 0
    for n in range(1, 6):
        full = tensor([rho]*n)
        ave = scale(Q(0), tensor([I]*n))
        for i in range(n):
            ave = add(ave, scale(Q(1,n), tensor([I]*i + [C] + [I]*(n-i-1))))
        assert tr(mul(full, mul(tuple(zip(*ave)), ave))) == 4*b*b/n


if __name__ == "__main__":
    groups = ((2, 2), (2, 2, 2), (2, 4), (3, 3))
    checks = [subgroup_checks(g) for g in groups]
    entropy_example()
    pauli_and_tensor()
    print("PASS: subgroup counts", tuple(a for a, b in checks),
          "; exact coset identities", sum(b for a, b in checks))
    print("PASS: exact entropy-root bounds 19/40 < b < 12/25")
    print("PASS: Pauli covariance determinant and five tensor GNS identities")
