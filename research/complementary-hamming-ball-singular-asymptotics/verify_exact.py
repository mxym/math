#!/usr/bin/env python3
"""Integer Walsh/sector trace checks, and exact small projection-DPP checks."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def kraw(n, x, y):
    return sum((-1)**t * choose(x, t) * choose(n-x, y-t) for t in range(y+1))


def ab(A, B):
    columns = tuple(zip(*B))
    return [[sum(a*b for a, b in zip(row, col)) for col in columns] for row in A]


def powers_trace(A, count):
    M, result = A, []
    for i in range(count):
        result.append(sum(M[j][j] for j in range(len(M))))
        if i + 1 < count:
            M = ab(M, A)
    return result


def det(A):
    B = [list(map(Q, row)) for row in A]
    n, value = len(B), Q(1)
    for j in range(n):
        k = next((k for k in range(j, n) if B[k][j]), None)
        if k is None:
            return Q(0)
        if k != j:
            B[k], B[j] = B[j], B[k]
            value = -value
        d = B[j][j]
        value *= d
        for i in range(j+1, n):
            f = B[i][j] / d
            for k in range(j+1, n):
                B[i][k] -= f * B[j][k]
    return value


def sector_checks():
    matrices, comparisons = 0, 0
    for n in range(1, 8):
        ranges = [[z for z in range(1 << n) if z.bit_count() <= a]
                  for a in range(n//2+1)]
        for a, X in enumerate(ranges):
            for b, Y in enumerate(ranges):
                H = [[(-1)**((x & y).bit_count() % 2) for y in Y] for x in X]
                actual = powers_trace(ab(H, list(zip(*H))), 4)
                want = [0]*4
                for r in range(min(a,b)+1):
                    m = n-2*r
                    L = [[kraw(m,x,y) for y in range(b-r+1)] for x in range(a-r+1)]
                    R = [[kraw(m,y,x) for x in range(a-r+1)] for y in range(b-r+1)]
                    mult = choose(n,r)-choose(n,r-1)
                    for k, tr in enumerate(powers_trace(ab(L,R),4),1):
                        want[k-1] += mult * 2**(2*r*k) * tr
                assert actual == want, (n,a,b,actual,want)
                if min(a,b)==0:
                    assert actual[0] == sum(comb(n,j) for j in range(max(a,b)+1))
                    assert actual[3] == actual[0]**4
                matrices += 1
                comparisons += len(actual)
    return matrices, comparisons


def dpp_checks():
    cuts, atoms = 0, 0
    for n in range(1,7):
        for b in range(n//2+1):
            X = range(n+1)
            F = [[kraw(n,x,y) for y in range(b+1)] for x in X]
            T = [[kraw(n,y,x) for x in X] for y in range(b+1)]
            P = [[Q(x,2**n) for x in row] for row in ab(F,T)]
            assert ab(P,P)==P
            law = {}
            for S in combinations(X,b+1):
                atom = det([[P[i][j] for j in S] for i in S])
                assert atom >= 0
                law[S] = atom
                atoms += 1
            assert sum(law.values()) == 1
            for a in range(n//2+1):
                avoid = sum(w for S,w in law.items() if S[0]>a)
                C = [[int(i==j)-P[i][j] for j in range(a+1)] for i in range(a+1)]
                assert avoid==det(C)
                cuts += 1
    return cuts, atoms


m, t = sector_checks()
print(f"exact full-Walsh versus spin sectors: {m} cut pairs, {t} trace powers")
c, d = dpp_checks()
print(f"exact radial projection DPP: {c} gap events, {d} nonnegative atom weights")
