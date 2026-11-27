#!/usr/bin/env python3
"""Direct punctured-codeword enumeration; no parity-check or error syndrome steps."""
from itertools import combinations, product


class Field:
    def __init__(self, q):
        self.q = q

    def add(self, a, b):
        return a ^ b if self.q == 4 else (a + b) % self.q

    def mul(self, a, b):
        if self.q != 4:
            return a * b % self.q
        z = 0
        for j in range(2):
            if b & (1 << j):
                z ^= a << j
        return z ^ 7 if z & 4 else z

    def ev(self, coeffs, x):
        z = 0
        for a in reversed(coeffs):
            z = self.add(self.mul(z, x), a)
        return z


def rows(C, n, r):
    packs = []
    for k in range(n-r, n+1):
        for T in combinations(range(n), k):
            assert T
            packs.append((T, {tuple(c[i] for i in T) for c in C}))
    return packs


def bad_set(F, U, S, projected):
    n = len(U[0])
    open_views = [(T, P) for T, P in projected
                  if any(tuple(u[i] for i in T) not in P for u in U)]
    return {x for x in S if any(tuple(F.ev(tuple(u[i] for u in U), x) for i in T) in P
                                for T, P in open_views)}


def max_repetition(q, n, d, r, S):
    F = Field(q)
    C = [(x,)*n for x in range(q)]
    P = rows(C, n, r)
    # Translating each coefficient by a codeword preserves every punctured test.
    # Normalize its first coordinate to zero; enumerate one representative per coset.
    reps = [(0,) + a for a in product(range(q), repeat=n-1)]
    return max(len(bad_set(F, U, S, P)) for U in product(reps, repeat=d+1)), len(reps)**(d+1)


def main():
    total_tuples = 0
    rep_cases = (
        (5, 3, 1, 1, range(5), 3),
        (3, 3, 1, 1, (1, 2), 2),
        (5, 4, 1, 1, range(5), 2),
        (3, 4, 2, 1, range(3), 3),
        (2, 5, 2, 1, range(2), 2),
        (2, 3, 1, 0, range(2), 1),
        (3, 5, 1, 2, (0, 2), 2),
    )
    for q, n, d, r, S, expected in rep_cases:
        got, count = max_repetition(q, n, d, r, S)
        assert got == expected, (q,n,d,r,S,got,expected)
        total_tuples += count

    # Explicit non-profile lift in characteristic 2, despite r=2 dividing the characteristic.
    # F4 GF(2)[X]/(X^2+X+1); base [4,2,3] evaluation code.
    F = Field(4)
    S = range(4)
    base = [tuple(F.ev((a, b), x) for x in S) for a, b in product(S, repeat=2)]
    assert min(sum(v != 0 for v in c) for c in base if any(c)) == 3
    # Find a full-four-exception tuple using only direct punctured restrictions.
    # Each coefficient translated so that its values at zero and one vanish.
    reps = [(0, 0, a, b) for a,b in product(S, repeat=2)]
    P0 = rows(base, 4, 1)
    U = next(U for U in product(reps, repeat=2) if bad_set(F, U, S, P0) == set(S))
    lift = lambda v: tuple(y for a in v for y in (a, a)) + (0,)
    C = list(map(lift, base))
    assert min(sum(v != 0 for v in c) for c in C if any(c)) == 6
    assert bad_set(F, list(map(lift, U)), S, rows(C, 9, 2)) == set(S)
    assert bad_set(F, list(map(lift, U)), S, rows(C, 9, 1)) == set()

    F = Field(5)
    C = [(x,)*3 for x in range(5)]
    U = [(0,0,1), (0,1,2)]
    B = bad_set(F, U, range(5), rows(C, 3, 1))
    assert B == {0,2,4} and len(B) > 2
    CA = any(all(tuple(u[i] for i in T) in P for u in U)
             for T,P in rows(C,3,1))
    assert not CA
    F7 = Field(7)
    C5 = [(x,)*5 for x in range(7)]
    degree2 = [(2,5,0,0,0),(4,0,0,0,0),(1,1,0,0,0)]
    assert bad_set(F7,degree2,range(7),rows(C5,5,1)) == {1,2,3,4}
    C4 = [(x,)*4 for x in range(5)]
    strict = [(4,3,0,0),(1,1,0,0)]
    assert bad_set(F,strict,range(5),rows(C4,4,1)) == {1,2}
    W = [(0,0,0,0),(1,0,0,0)]
    assert bad_set(F,W,range(5),rows(C4,4,1)) == {0}
    # Padding the singleton's zero error to erase its active coordinate hides the exception.
    assert bad_set(F,W,range(5),[row for row in rows(C4,4,1) if row[0] == (1,2,3)]) == set()
    print(f'Direct codeword projections: {len(rep_cases)} exhaustive tables, {total_tuples} coefficient tuples')
    print('Characteristic-two repeated blocks: 4 exact exceptions at r=2, none at r=1')
    print('Degree-two uncapped root profile: 4 exact exceptions')
    print('F5 source checks: endpoint labels 0,2,4; strict bound labels 1,2; padded-witness negative control PASS')


if __name__ == '__main__':
    main()
