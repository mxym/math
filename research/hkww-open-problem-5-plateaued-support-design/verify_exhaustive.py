#!/usr/bin/env python3
"""Full incidence checks on all nonlinear, non-bent 3- and 4-bit functions."""
from collections import Counter

if not __debug__:
    raise RuntimeError("Run without -O")


def fwt(data):
    ans = list(data)
    step = 1
    while step < len(ans):
        for i in range(0, len(ans), step*2):
            for j in range(i, i+step):
                left, right = ans[j], ans[j+step]
                ans[j], ans[j+step] = left+right, left-right
        step *= 2
    return ans


def pair_regular(blocks, v):
    full = (1 << v) - 1
    for b in blocks:
        assert b & full == b
    return len({
        sum(b & (1 << i | 1 << j) == (1 << i | 1 << j) for b in blocks)
        for j in range(v) for i in range(j)
    }) == 1


def enumerate_m(m):
    counts = Counter()
    N = 1 << m
    for f in range(1 << N):
        bits = [(f >> i) & 1 for i in range(N)]
        W = fwt(1-2*b for b in bits)
        magnitudes = {abs(w) for w in W if w != 0}
        if len(magnitudes) != 1:
            continue
        S = {a for a, w in enumerate(W) if w != 0}
        if len(S) == 1 or len(S) == N:
            continue
        R = m - (len(S).bit_length()-1)
        D = [i for i, b in enumerate(bits) if b]
        v = len(D)
        full = (1 << v) - 1
        positive = []
        zero = []
        for a in range(1, N):
            cut = sum((((a & x).bit_count() % 2) << i) for i, x in enumerate(D))
            if a not in S:
                zero += [cut, cut ^ full]
            elif W[a] > 0:
                positive.append(cut)
            else:
                positive.append(cut ^ full)
        negative = [cut ^ full for cut in positive]
        expected = (
            R == 1 and any(
                S == {a for a in range(N) if (a & t).bit_count() % 2}
                for t in range(1, N)
            )
        )
        degenerate = len(S) == 4 and W[0] > 0
        good = expected or degenerate
        for family in (positive, negative, zero):
            assert len({cut.bit_count() for cut in family}) == 1
            assert pair_regular(family, v) == good
            assert pair_regular(set(family), v) == good
        counts["plateaued"] += 1
        counts["surviving"] += int(expected)
        counts["full-plus exception"] += int(degenerate)
    return counts


if __name__ == "__main__":
    desired = {
        3: {"plateaued": 112, "surviving": 56, "full-plus exception": 28},
        4: {"plateaued": 1120, "surviving": 0, "full-plus exception": 140},
    }
    for m in (3, 4):
        counts = enumerate_m(m)
        assert counts == desired[m], (m, counts)
        print(f"m={m}: all {1 << (1 << m)} tables, {dict(counts)} PASS")
