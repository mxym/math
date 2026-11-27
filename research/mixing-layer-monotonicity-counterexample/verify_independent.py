#!/usr/bin/env python3
"""Independent enumeration of all 64^3 key triples and full output pairs."""
from collections import Counter
from fractions import Fraction

S = (0, 4, 7, 2, 3, 5, 6, 1)
DELTA = 3 | (3 << 3)


def layer(x, key):
    return S[(x & 7) ^ (key & 7)] | (S[(x >> 3) ^ (key >> 3)] << 3)


def shear(x):
    a, b = x & 7, x >> 3
    return a | ((a ^ b) << 3)


def cipher(x, k0, k1, k2, mixed):
    x = layer(x, k0)
    if mixed:
        x = shear(x)
    x = layer(x, k1)
    return layer(x, k2)


def distribution(mixed):
    count = Counter()
    for k0 in range(64):
        for k1 in range(64):
            for k2 in range(64):
                a = cipher(0, k0, k1, k2, mixed)
                b = cipher(DELTA, k0, k1, k2, mixed)
                assert a != b
                count[a, b] += 1
    assert sum(count.values()) == 64 ** 3
    return count


def tv(count):
    ideal = Fraction(1, 64 * 63)
    return sum(abs(Fraction(count[a, b], 64 ** 3) - ideal)
               for a in range(64) for b in range(64) if a != b) / 2


plain = distribution(False)
mixed = distribution(True)
assert len(plain) == 2304
assert len(mixed) == 1920
assert Counter(plain.values()) == Counter({64: 1024, 128: 1024, 256: 256})
assert Counter(mixed.values()) == Counter(
    {64: 1024, 128: 512, 256: 256, 512: 128})
assert tv(plain) == Fraction(109, 252)
assert tv(mixed) == Fraction(19, 36)
assert tv(mixed) - tv(plain) == Fraction(2, 21)

print("PASS full key enumeration no-mix:",
      64 ** 3, "keys", len(plain), "output pairs", tv(plain))
print("PASS full key enumeration shear:",
      64 ** 3, "keys", len(mixed), "output pairs", tv(mixed))
print("PASS independent full output-pair increase:", tv(mixed) - tv(plain))
