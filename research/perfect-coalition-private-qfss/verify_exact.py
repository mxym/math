#!/usr/bin/env python3
"""Enumerate complete coalition-query distributions and reconstruct data."""
from collections import Counter
from itertools import product, combinations


class GF:
    def __init__(self,q):
        self.q = q
        m = {4:7,8:11}[q]
        def mul(a,b):
            c = 0
            while b:
                if b & 1:
                    c ^= a
                a <<= 1
                b >>= 1
                if a & q:
                    a ^= m
            return c
        self.M = tuple(tuple(mul(a,b) for b in range(q)) for a in range(q))
        self.inv = (0,) + tuple(self.M[a].index(1) for a in range(1,q))

    def points(self,values,x):
        a = 0
        for c in values[::-1]:
            a = self.M[a][x] ^ c
        return a

    def lagrange(self,xs):
        W = []
        for x in xs:
            z = 1
            for y in xs:
                if x != y:
                    z = self.M[z][self.M[y][self.inv[x ^ y]]]
            W.append(z)
        return W

    def selectors(self,v,Z):
        W = []
        for z in Z:
            f = 1
            for x,b in zip(v,z):
                f = self.M[f][x if b else 1 ^ x]
            W.append(f)
        return W

    def dot(self,a,b):
        z = 0
        for u,v in zip(a,b):
            z ^= self.M[u][v]
        return z


def exhaustive(q,L,t,B):
    F = GF(q)
    p = L*t+1
    X = tuple(range(1,p+1))
    Z = tuple(product((0,1),repeat=L))
    D = len(Z)
    C = [tuple(c) for k in range(t+1) for c in combinations(range(p),k)]
    W = F.lagrange(X)
    S = {v:F.selectors(v,Z) for v in product(range(q),repeat=L)}
    assert all(sum(1 for u in S[z] if u) == 1 and S[z][i] == 1
               for i,z in enumerate(Z))
    # At least one record >1 in the test data; integers are binary labels modulo no prime.
    tables = [tuple((j*j + c*(j+1) + 1) % (B+1) for j in range(D))
              for c in range(4)]
    count = 0
    atoms = 0
    for j,z in enumerate(Z):
        H = {I:Counter() for I in C}
        for R in product(range(q),repeat=t*L):
            P = [(z[i],)+R[i*t:(i+1)*t] for i in range(L)]
            V = [tuple(F.points(c,x) for c in P) for x in X]
            for I,Y in H.items():
                Y[tuple(V[i] for i in I)] += 1
            for T in tables:
                values = [F.dot(T,S[v]) for v in V]
                assert F.dot(W,values) == T[j]
                count += 1
        for I,Y in H.items():
            k = len(I)
            assert len(Y) == q**(k*L)
            assert set(Y.values()) == {q**((t-k)*L)}
            atoms += len(Y)
    return count, atoms, len(C)


def main():
    cases = ((4,1,1,3),(4,2,1,3),(8,2,2,5),(4,2,0,3),(4,0,2,3))
    checked=atoms=cuts=0
    for item in cases:
        v,a,c = exhaustive(*item)
        checked += v
        atoms += a
        cuts += c
    print(f'Field checks: {len(cases)} cases, {checked} correct decodings, {cuts} coalition structures, {atoms} uniform view cells')
    print('Nonbinary record labels, empty-coalition, t=0 and L=0 controls PASS')


if __name__=='__main__':
    main()
