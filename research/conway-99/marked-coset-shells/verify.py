"""Finite checks for the marked coset and the endpoint-intersection argument."""

from fractions import Fraction
from itertools import product


def first_shells():
    eligible = []
    for norm in range(29):
        for residue in (1, 4, 7):
            if (norm - 2 * residue + 28) % 18 == 0:
                if 63 * norm >= 99 * residue * (9 - residue):
                    eligible.append((norm, residue))
    assert eligible == [(22, 7), (28, 1)]


def shell_profiles():
    unusual = (-4, -3, -2, 1, 2, 3)
    costs = [v * (v + 1) for v in unusual]
    count_ranges = [range(1 + 12 // cost) for cost in costs]
    survivors = set()
    for counts in product(*count_ranges):
        if sum(c * n for c, n in zip(costs, counts)) != 12:
            continue
        values = [v for v, n in zip(unusual, counts) for _ in range(n)]
        num_negative_ones = 11 + sum(values)
        num_zeros = 99 - len(values) - num_negative_ones
        if min(num_negative_ones, num_zeros) < 0:
            continue
        values.extend([-1] * num_negative_ones + [0] * num_zeros)
        assert sum(values) == -11 and sum(v * v for v in values) == 23
        for v in set(values):
            neighbors = sorted(values)
            neighbors.remove(v)
            if not sum(neighbors[:14]) <= -4 * v - 2 <= sum(neighbors[-14:]):
                break
        else:
            survivors.add(tuple(sorted((v, values.count(v)) for v in set(values) - {0})))
    assert survivors == {
        ((-1, 14), (3, 1)),
        ((-1, 15), (2, 2)),
        ((-1, 16), (1, 3), (2, 1)),
        ((-1, 17), (1, 6)),
    }
    assert 2 * 10 - 15 > 2


def endpoint_intersections():
    allowed = set()
    for a in range(8):
        for b in range(a + 1):
            if b >= 2 or (b == 1 and a > 3):
                continue
            y, x = 3 * (a + b) - 6, 28 - 4 * (a + b)
            if 0 <= y <= 15 and 0 <= x <= 70 and y + a <= 15:
                allowed.add((y + b, y + a))
    assert allowed == {(1, 1), (0, 2), (3, 6), (6, 10), (9, 14), (4, 5), (7, 9)}
    ordered = allowed | {(b, a) for a, b in allowed}
    orthogonal = [
        (a, b, c, d) for a, b in ordered for c, d in ordered
        if (a, c) in ordered and (b, d) in ordered and a + d == b + c
    ]
    assert orthogonal == [(1, 1, 1, 1)]
    for p in range(1, 45):
        common = Fraction(22**2, 99)
        norm = 2 * p * ((22 - common) + (15 - common) + (2 * p - 2) * (1 - common))
        assert norm == Fraction(2 * p * (315 - 70 * p), 9)
        assert (norm >= 0) == (p <= 4)


if __name__ == "__main__":
    first_shells()
    shell_profiles()
    endpoint_intersections()
    print("Verified the two shell norms, four candidate profiles, and four-pair bound.")
