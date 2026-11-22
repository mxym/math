"""Replay exact raw/free subset sums against the split parity formulas."""
from fractions import Fraction as F
from random import Random


def subsets(n):
    return range(1 << n)


def sublabels(mask):
    bits = mask
    while True:
        yield bits
        if bits == 0:
            return
        bits = (bits - 1) & mask


def mob(mask):
    return -1 if mask.bit_count() % 2 else 1


def add(logs, mask):
    return sum(z for i, z in enumerate(logs) if (mask >> i) & 1)


def literal(logs, k, g):
    full = (1 << len(logs)) - 1
    small = (1 << k) - 1
    total = sum(logs)
    out = 0
    for mask in subsets(len(logs)):
        a = add(logs, mask)
        if a > F(total, 2) - g:
            out += mob(mask) * (total - a)
        if a > F(total, 2) + g:
            b = full ^ mask
            for c in sublabels(b & small):
                out += (-2) ** c.bit_count() * add(logs, b ^ c)
    return out


def averaged_literal(logs, k, gaps):
    return sum(weight * literal(logs, k, gap) for gap, weight in gaps)


def model_two(cloud, p, q, gaps):
    k, s = len(cloud), sum(cloud)
    total = p + q + s
    first = 2 * s if k == 1 else 0
    second = 0
    raw_events = 0
    for mask in subsets(k):
        a = add(cloud, mask)
        z = F(2 * (p + a) - total, 2)
        raw = sum(weight for gap, weight in gaps if abs(z) < gap)
        raw_events += bool(raw)
        right = (1 - raw) if z > 0 else 0
        if k % 2 == 0:
            second += mob(mask) * ((2 * a - total) * raw + (4 * a - 2 * s) * right)
        else:
            second += mob(mask) * ((2 * a - total) * raw - 2 * (total - s) * right)
    return first + second, raw_events


def check():
    rng = Random(20713)
    gaps = ((F(53, 3), F(2, 7)), (F(79, 3), F(3, 7)), (F(100, 3), F(2, 7)))
    twos = ones = crossings = 0
    for k in range(9):
        for _ in range(130):
            cloud = [rng.randrange(2, 45) for _ in range(k)]
            # One very large macro, all short sides genuinely safe.
            whole_one = averaged_literal(cloud + [10_000], k, gaps)
            if whole_one != 0:
                raise ValueError(("one-macro", cloud, whole_one))
            ones += 1

            p = rng.randrange(4600, 5000)
            q = p + rng.randrange(1, min(325, 25 + sum(cloud)))
            expected, count = model_two(cloud, p, q, gaps)
            actual = averaged_literal(cloud + [p, q], k, gaps)
            if actual != expected:
                raise ValueError(("two-macro", cloud, p, q, actual, expected))
            twos += 1
            crossings += count
    print(f"exact one-macro rows {ones}; two-macro rows {twos}; actual raw pair hits {crossings}")


if __name__ == "__main__":
    check()
