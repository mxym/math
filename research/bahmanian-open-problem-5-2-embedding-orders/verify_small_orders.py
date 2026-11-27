#!/usr/bin/env python3
"""Exhaustive independent check of ordinary small-order minima."""

from collections import Counter
from itertools import permutations

if not __debug__:
    raise RuntimeError("Run without -O")


def complete_latin_squares(n):
    """Every full labelled Latin square, using all row permutations."""
    perms = list(permutations(range(1, n+1)))
    stack = []
    used = [set() for _ in range(n)]

    def search():
        if len(stack) == n:
            yield tuple(stack)
            return
        for row in perms:
            if any(x in allowed for x, allowed in zip(row, used)):
                continue
            for x, allowed in zip(row, used):
                allowed.add(x)
            stack.append(row)
            yield from search()
            stack.pop()
            for x, allowed in zip(row, used):
                allowed.remove(x)
    yield from search()


def partial_codes(r):
    """All labelled partial r-squares, cellwise row/column admissibility."""
    base = r+1
    C, R = [0]*r, [0]*r

    def rec(t, place, code):
        if t == r*r:
            yield code
            return
        i, j = divmod(t, r)
        yield from rec(t+1, place*base, code)  # vacant cell
        valid = ((1 << base)-2) & ~(R[i] | C[j])
        while valid:
            d = valid & -valid
            valid ^= d
            R[i] ^= d
            C[j] ^= d
            yield from rec(t+1, place*base, code+(d.bit_length()-1)*place)
            R[i] ^= d
            C[j] ^= d
    yield from rec(0, 1, 0)


def mark_targets(r, n, bitset):
    base = r+1
    traces = set()
    full_count = 0
    bit = 1 << (n-r)
    for L in complete_latin_squares(n):
        full_count += 1
        trace = tuple(L[i][j] if L[i][j] <= r else 0
                      for i in range(r) for j in range(r))
        traces.add(trace)
    for tr in traces:
        subcodes = [0]
        for i, x in enumerate(tr):
            if x:
                delta = x*base**i
                subcodes += [c+delta for c in subcodes]
        for c in subcodes:
            bitset[c] |= bit
    return full_count


def check(r):
    all_masks = bytearray((r+1)**(r*r))
    counts = [mark_targets(r, n, all_masks) for n in range(r, 2*r)]
    expected_ls = {2: [2, 12], 3: [12, 576, 161280]}
    assert counts == expected_ls[r]
    classes = Counter(all_masks[code] for code in partial_codes(r))
    assert 0 not in classes
    min_order_counts = Counter()
    for mask, c in classes.items():
        least = (mask & -mask).bit_length()-1+r
        min_order_counts[least] += c
    expected = {
        2: {2: 31, 3: 4},
        3: {3: 5836, 4: 5886, 5: 54},
    }
    assert min_order_counts == expected[r], (r, min_order_counts, classes)
    print(f"r={r}: {sum(classes.values())} labelled partial squares; target "
          f"Latin-square enumeration {counts}; minimum-order histogram "
          f"{dict(sorted(min_order_counts.items()))} PASS")


if __name__ == "__main__":
    check(2)
    check(3)
