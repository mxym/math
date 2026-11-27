#!/usr/bin/env python3
"""Check two exact row identities for the hypersimplex obstruction.

No dependencies beyond Python's standard library.  Coordinates and row
coefficients are integers; both identities are multiplied by 10.
"""
from itertools import combinations

edges = list(combinations(range(5), 2))
edge_index = {e: i for i, e in enumerate(edges)}


def unit(i):
    return tuple(int(i == j) for j in range(5))


def diag(e, f):
    return tuple(int(j in e) - int(j in f) for j in range(5))


def row(pair, other, v):
    ans = [0] * 40
    for e, sign in zip(pair + other, (1, 1, -1, -1)):
        i = edge_index[e]
        for j in range(4):
            ans[4 * i + j] += sign * (v[j] - v[4])
    return ans


B, L = [], []
for missing in range(5):
    a, b, c, d = [i for i in range(5) if i != missing]
    pairs = (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c)))
    for p, q in combinations(pairs, 2):
        B.extend((row(p, q, diag(*p)), row(p, q, diag(*q))))
        L.append(tuple(row(p, q, unit(k)) for k in range(5)))

# These represent coordinate 0 or 4 of the first pairing minus the
# second pairing on {0,1,2,3}; S_5 transports them to every output.
data = (
    (0, ((7,-1),(8,-1),(10,-1),(13,1),(14,1),(16,1),
         (24,2),(25,2),(27,2),(29,-2)), 14),
    (4, ((0,-2),(2,2),(4,1),(5,-1),(7,2),(8,1),(9,-1),
         (10,2),(13,-2),(14,-1),(15,1),(16,-2),(18,-1),(19,-1),
         (21,2),(23,-2)), 24),
)
assert len(B) == 30 and len(L) == 15
for k, terms, budget in data:
    assert sum(abs(c) for _, c in terms) == budget
    assert all(sum(c * B[r][j] for r, c in terms) == 10 * L[12][k][j]
               for j in range(40))

# 6 * sqrt(340)/5 < 23, the rational radius in the note is valid.
assert 36 * 340 < 23**2 * 25

# Check the 10 base sites have 300 acute and 60 right angles.
base = [tuple(int(i in e) for i in range(5)) for e in edges]
angles = []
for b, Y in enumerate(base):
    for a, c in combinations((i for i in range(10) if i != b), 2):
        angles.append(sum((X-y)*(Z-y) for X,y,Z in zip(base[a],Y,base[c])))
assert len(angles) == 360 and min(angles) == 0 and angles.count(0) == 60
print("Verified: 30 projected rows, 15 differences, two exact identities, radius 1/23.")
