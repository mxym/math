#!/usr/bin/env python3
"""Exact formal Frobenius-orbit and polynomial-matrix checks over F_2."""
from itertools import product

# Frobenius variables are pairs (name, q-index modulo 6).
X = lambda i: ("x", i % 6)
Y = lambda i: ("y", i % 6)
Z = lambda i: ("z", i % 6)


def xor(items):
    s = set()
    for item in items:
        if item in s:
            s.remove(item)
        else:
            s.add(item)
    return s


def psi(v):
    return [(v(0), v(1)), (v(1), v(3)), (v(3), v(4))]


def frobenius_trace(terms):
    return xor(tuple(sorted((label, (i + j) % 6) for label, i in term))
               for term in terms for j in range(6))


def shear(terms, exponent):
    for term in terms:
        yield from product(*([(Z(i), Y(i + exponent)) if label == "x"
                              else (Y(i),) for label, i in term]))


# Polynomial matrices: entries are sets of monomials, and a monomial is
# a sorted tuple of free indeterminates (with repeated powers retained).
one = {()}
zero = set()


def mul(*factors):
    return xor(tuple(sorted(sum(m, ()))) for m in product(*factors))


def mm(a, b):
    return [[mul(a[i][0], b[0][j]) ^ mul(a[i][1], b[1][j])
             for j in (0, 1)] for i in (0, 1)]


def main():
    h = (Y(0), Y(1), Y(2))
    original = [p + (Y(0),) for p in psi(X)] + [h]
    target = frobenius_trace([p + (Y(0),) for p in psi(Z)])
    assert frobenius_trace(shear(original, 4)) == target
    assert len(target) == 18  # not a vacuous zero-versus-zero identity
    assert frobenius_trace(shear(original, 3)) != target
    mutant = original[:-1] + [(Y(0), Y(1), Y(3))]
    assert frobenius_trace(shear(mutant, 4)) != target

    # Three symbolic matrices with distinct parameters, and a free constant b.
    b = {("b",)}
    A = [[one, one], [zero, one]]
    B = [[zero, b], [one, zero]]
    I = [[one, zero], [zero, one]]
    assert mm(A, A) == I
    assert mm(B, B) == [[b, zero], [zero, b]]
    assert [[s ^ t for s, t in zip(r, u)]
            for r, u in zip(mm(A, B), mm(B, A))] == I
    def make(z):
        zz = {(z,)}
        return [[zz, zz ^ b], [one, zz]]
    m = mm(mm(make("z0"), make("z1")), make("z2"))
    u, v = m[0][0], m[1][0]
    assert m == [[u, u ^ mul(v, b)], [v, u]]
    assert u and v
    print("PASS: 18-term symbolic trace identity; both exponent/shear mutants rejected")
    print("PASS: symbolic odd-product matrix identities over F_2[b,z0,z1,z2]")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Do not run with Python -O.")
    main()
