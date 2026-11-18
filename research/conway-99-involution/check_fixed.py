"""Enumerate the local types of a fixed vertex of a putative Conway involution."""
from collections import defaultdict
from math import comb


def profiles(total, types):
    if len(types) == 1:
        yield [(total, types[0])]
        return
    for n in range(total + 1):
        for rest in profiles(total - n, types[1:]):
            yield [(n, types[0]), *rest]


def main():
    types = defaultdict(list)
    for a in range(7):
        for c in range((7 - a) // 2 + 1):
            b = 7 - a - 2 * c
            f = 1 + 2 * a + comb(2 * a, 2) - a + 2 * c
            assert f == 1 + 2 * a * a + 2 * c
            types[f].append((a, b, c))
    surviving = []
    for f, local in sorted(types.items()):
        n = (99 - f) // 2
        for profile in profiles(f, local):
            a_sum, e, p = [sum(count * t[i] for count, t in profile) for i in range(3)]
            d = n - e - p
            if a_sum % 3 or d < 0 or d % 2 or (4 * n - e) % 7:
                continue
            surviving.append((f, n, e, p, d))
    assert surviving == [(1, 49, 7, 0, 42)]
    print('Locally possible fixed-set sizes:', *sorted(types))
    print('Surviving (fixed, two-point orbits, adjacent, two fixed neighbours, no fixed neighbour):',
          surviving[0])


if __name__ == '__main__':
    main()
