#!/usr/bin/env python3
"""Direct finite-field evaluation on every small subspace, independent of verifier A."""
from collections import Counter
from fractions import Fraction as F
from itertools import product


class Field:
    """Elements are packed coefficients of a monic polynomial quotient."""
    def __init__(self, base, mod):
        self.base, self.mod = base, mod
        self.degree = len(mod)
        self.q0 = base.order
        self.order = self.q0**self.degree
        self.digits = [tuple((x//self.q0**j) % self.q0 for j in range(self.degree))
                       for x in range(self.order)]
        self.add = [[self.pack(base.add[a][b] for a, b in zip(A, B))
                     for B in self.digits] for A in self.digits]
        self.mul = [[self.multiply(A, B) for B in self.digits] for A in self.digits]
        assert all(1 in self.mul[x] for x in range(1, self.order))

    def pack(self, coeffs):
        return sum(c*self.q0**i for i, c in enumerate(coeffs))

    def multiply(self, A, B):
        h = [0]*(2*self.degree-1)
        add, mul = self.base.add, self.base.mul
        for i, a in enumerate(A):
            for j, b in enumerate(B):
                h[i+j] = add[h[i+j]][mul[a][b]]
        for i in reversed(range(self.degree, len(h))):
            for j, c in enumerate(self.mod):
                dest = i-self.degree+j
                h[dest] = add[h[dest]][mul[h[i]][self.base.neg[c]]]
        return self.pack(h[:self.degree])

    def power(self, x, n):
        y = 1
        while n:
            if n & 1:
                y = self.mul[y][x]
            x = self.mul[x][x]
            n >>= 1
        return y

    @property
    def neg(self):
        return [row.index(0) for row in self.add]


class Prime:
    def __init__(self, p):
        self.order = p
        self.add = [[(i+j) % p for j in range(p)] for i in range(p)]
        self.mul = [[i*j % p for j in range(p)] for i in range(p)]
        self.neg = [(-i) % p for i in range(p)]


def spaces(K):
    q = K.q0
    levels = [{frozenset({0}): ()}]
    for d in range(K.degree):
        new = {}
        for U, basis in levels[-1].items():
            for x in range(1, K.order):
                if x in U:
                    continue
                V = frozenset(K.add[u][K.mul[t][x]] for u in U for t in range(q))
                assert len(V) == q**(d+1)
                new[V] = basis + (x,)
        levels.append(new)
    return levels


def check(base, modulus):
    K = Field(base, modulus)
    groups = spaces(K)
    q, k = K.q0, K.degree
    for r in range(1, k+1):
        m = min(r, 3) if q == 2 else 1
        powers = [[K.power(x, q**j) for j in range(m)] for x in range(K.order)]
        rows = []
        for a in product(range(K.order), repeat=m):
            values = []
            for xx in powers:
                y = 0
                for b, x in zip(a, xx):
                    y = K.add[y][K.mul[b][x]]
                values.append(y % q**r)
            rows.append(values)
        for s in range(1, m+1):
            for basis in groups[s].values():
                hist = Counter(tuple(row[x] for x in basis) for row in rows)
                assert len(hist) == q**(r*s)
                assert set(hist.values()) == {len(rows)//q**(r*s)}
                # In the multiset with 24 copies of all coefficients plus
                # one extra zero, every nontrivial character mean is 1/N.
                count = hist[(0,)*s]
                N = 24*len(rows)+1
                assert F(24*count+1, N)-F(1, q**(r*s)) == F(1, N)*(1-F(1, q**(r*s)))
                assert N >= 24*q**(r*(3 if q == 2 else 1))
        good = [sum(len({row[x] for x in U}) == q**r for row in rows) for U in groups[r]]
        target = F(1, 8) if q == 2 else F(23, 48)
        assert F(24*min(good), 24*len(rows)+1) >= target
        print(f"evaluation q={q} k={k} r={r} m={m} coefficients={len(rows)} "
              f"spaces={len(groups[r])} min_success={F(min(good), len(rows))}")


if __name__ == "__main__":
    two, three = Prime(2), Prime(3)
    check(two, [1, 1, 0, 0])        # X^4 + X + 1 over F2
    check(three, [1, 2, 0])         # X^3 - X + 1 over F3
    four = Field(two, [1, 1])       # F4 based on rho^2 + rho + 1
    check(four, [2, 1])             # X^2 + X + rho over F4
    print("evaluation PASS")
