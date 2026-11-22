"""Exact arithmetic replay of generic macro allocation and safe projection."""
from fractions import Fraction as F
from math import factorial
from random import Random


def mobs(mask):
    return (-1) ** mask.bit_count()


def mask_sums(labels):
    out = [0]
    for value in labels:
        out.extend(x + value for x in out[:])
    return out


def sublabels(mask):
    bits = mask
    while True:
        yield bits
        if not bits:
            return
        bits = (bits - 1) & mask


def literal(cloud, macro, gaps):
    labels = cloud + macro
    logs = mask_sums(labels)
    T = logs[-1]
    full, small = (1 << len(labels)) - 1, (1 << len(cloud)) - 1
    score = F(0)
    for g, w in gaps:
        for mask, t in enumerate(logs):
            if t > F(T, 2) - g:
                score += w * mobs(mask) * (T - t)
            if t > F(T, 2) + g:
                b = full ^ mask
                for c in sublabels(b & small):
                    score += w * (-2) ** c.bit_count() * logs[b ^ c]
    return score


def modeled(cloud, macro, gaps):
    asums, usums = mask_sums(cloud), mask_sums(macro)
    s, T = asums[-1], asums[-1] + usums[-1]
    sigma = mobs(len(asums) - 1)
    other = len(usums) - 1
    score = F(0)
    hits = 0
    for m, u in enumerate(usums):
        if m > (other ^ m):
            continue
        al, be = mobs(m), mobs(other ^ m)
        eta = al * be * sigma
        for i, a in enumerate(asums):
            z = F(2 * (u + a) - T, 2)
            raw_gate = sum(w for g, w in gaps if abs(z) < g)
            right_gate = (1 - raw_gate) if z > 0 else 0
            R = al * T + (be * sigma - al) * (u + a)
            B0 = (1 + eta * al) * u + (eta * al - 1) * a
            B1 = sigma * ((1 + eta * be) * (T - s - u) + (eta * be - 1) * (s - a))
            score += mobs(i) * (B0 + (R - B0) * raw_gate + (B1 - B0) * right_gate)
            hits += bool(raw_gate)
    return score, hits


def bare_safe_and_raw(macro, gaps):
    logs = mask_sums(macro)
    T, full = logs[-1], len(logs) - 1
    safe = raw = F(0)
    for i, d in enumerate(logs):
        if i > (full ^ i):
            continue
        j = full ^ i
        if logs[j] < d:
            i, j = j, i
            d = logs[i]
        depth = F(T, 2) - d
        weights = sum(w for g, w in gaps if depth < g)
        safe += (1 - weights) * (1 + mobs(j)) * d
        raw += weights * (mobs(i) * logs[j] + mobs(j) * d)
    return safe, raw


def ceil_certify():
    # log(.502/.07) < 2 via a finite positive Taylor sum for e^2.
    e2_lower = sum(F(2**j, factorial(j)) for j in range(9))
    if not e2_lower > F(251, 35):
        raise ValueError("entropy estimate")
    if F(7, 100) * (1 + 2) != F(21, 100):
        raise ValueError("entropy exponent")
    if F(1, 4) - F(21, 100) <= F(3, 100):
        raise ValueError("no log-power slack")


def main():
    rng = Random(20261122)
    gaps = ((F(50, 3), F(2, 7)), (F(73, 3), F(3, 7)), (F(100, 3), F(2, 7)))
    tested = bare = crossings = 0
    for m in range(1, 8):
        for k in range(6):
            for rep in range(35):
                cloud = [rng.randrange(2, 80) for _ in range(k)]
                macro = [rng.randrange(512, 1500) for _ in range(m)]
                # Produce actual threshold crossings as well as far tails.
                if rep % 2 == 0 and m > 1:
                    h = rng.randrange(1, m)
                    macro[-1] = max(200, sum(macro[:h]) - sum(macro[h:-1])
                                       + rng.randrange(-160, 160))
                got = literal(cloud, macro, gaps)
                want, hits = modeled(cloud, macro, gaps)
                if got != want:
                    raise ValueError(("literal/model", cloud, macro, got, want))
                crossings += hits
                tested += 1
                if k == 0:
                    A, B = bare_safe_and_raw(macro, gaps)
                    if A < 0 or A + B != got:
                        raise ValueError(("safe projection", macro, A, B, got))
                    bare += 1
    ceil_certify()
    print(f"checked {tested} exact rows; {bare} no-small projections; {crossings} raw orbit hits")


if __name__ == "__main__":
    main()
