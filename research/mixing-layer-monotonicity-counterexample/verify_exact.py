#!/usr/bin/env python3
"""Exact DDT convolution for the three-layer two-word example."""
from collections import Counter
from fractions import Fraction

S = (0, 4, 7, 2, 3, 5, 6, 1)
assert sorted(S) == list(range(8))

D = [[0] * 8 for _ in range(8)]
for d in range(8):
    for u in range(8):
        D[d][S[u] ^ S[u ^ d]] += 1

EXPECTED = (
    (8, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 2, 2, 2, 2),
    (0, 0, 0, 0, 2, 2, 2, 2),
    (0, 0, 4, 4, 0, 0, 0, 0),
    (0, 4, 0, 4, 0, 0, 0, 0),
    (0, 0, 0, 0, 2, 2, 2, 2),
    (0, 0, 0, 0, 2, 2, 2, 2),
    (0, 4, 4, 0, 0, 0, 0, 0),
)
assert tuple(map(tuple, D)) == EXPECTED


def distribution(mixed):
    count = Counter()
    # First word differences a,b arise from initial difference (3,3).
    for a in range(8):
        for b in range(8):
            multiplicity = D[3][a] * D[3][b]
            if not multiplicity:
                continue
            x, y = (a, a ^ b) if mixed else (a, b)
            for c in range(8):
                for d in range(8):
                    add = multiplicity * D[x][c] * D[y][d]
                    if add:
                        count[c | (d << 3)] += add
    assert sum(count.values()) == 4096
    assert count[0] == 0
    return count


def histogram(count):
    return Counter(count.values())


def tv(count):
    return sum(abs(Fraction(count[i], 4096) - Fraction(1, 63))
               for i in range(1, 64)) / 2


plain = distribution(False)
shear = distribution(True)
assert len(plain) == 36
assert len(shear) == 30
assert histogram(plain) == Counter({64: 16, 128: 16, 256: 4})
assert histogram(shear) == Counter({64: 16, 128: 8, 256: 4, 512: 2})
assert tv(plain) == Fraction(109, 252)
assert tv(shear) == Fraction(19, 36)
assert tv(shear) - tv(plain) == Fraction(2, 21)

print(f"PASS DDT rows: {EXPECTED}")
print("PASS no-mix support/histogram/TV:",
      len(plain), sorted(histogram(plain).items()), tv(plain))
print("PASS shear support/histogram/TV:",
      len(shear), sorted(histogram(shear).items()), tv(shear))
print("PASS exact increase:", tv(shear) - tv(plain))
