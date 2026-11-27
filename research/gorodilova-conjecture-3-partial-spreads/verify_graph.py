#!/usr/bin/env python3
"""Literal plane counts for the F4 graph construction; no external input."""
from itertools import combinations
from math import comb

# 0, 1, w, w+1 with w^2+w+1=0; univariate product/traces.
def product(x, y):
    p = (x if y & 1 else 0) ^ ((x << 1) if y & 2 else 0)
    return p ^ (7 if p & 4 else 0)


def times_w(x, m):
    return sum(product(2, (x >> (2*i)) & 3) << (2*i) for i in range(m))


def graph(x, m):
    return x | ((product(x & 3, (x >> 2) & 3) >> 1) << (2*m))


def build(m):
    seen, lines = {0}, []
    for x in range(1, 1 << (2*m)):
        if x not in seen:
            y = times_w(x, m)
            assert x != y and times_w(x ^ y, m) == x
            orbit = {x, y, x ^ y}
            assert not seen.intersection(orbit)
            seen.update(orbit)
            T = tuple(sorted(graph(u, m) for u in orbit))
            assert T[0] ^ T[1] ^ T[2] == 0
            lines.append(T)
    assert len(lines) == ((1 << (2*m)) - 1)//3
    return tuple(lines)


def concurrence(lines, u, v):
    def in_kernel(x):
        return (x & u).bit_count() % 2 == (x & v).bit_count() % 2 == 0
    intersections = [sum(in_kernel(x) for x in T) for T in lines]
    assert all(k in (0, 1, 3) for k in intersections)
    return intersections.count(0), 1 + sum(intersections)


def check(m):
    n = 2*m + 1
    lines = build(m)
    points = {x for T in lines for x in T}
    assert len(points) == 3*len(lines)
    assert points == {graph(x, m) for x in range(1, 1 << (2*m))}
    assert 1 in points and 8 in points and 9 not in points
    # Computational regressions at larger n; all functionals at n=5,7.
    # The uniform result uses the proof and does not depend on these loops.
    masks = list(combinations(range(1, 1 << n), 2)) if n <= 7 else \
        list(combinations((1 << i for i in range(n)), 2))
    for u, v in masks:
        N0, count = concurrence(lines, u, v)
        assert N0 % 2 == count % 2 == 0
    assert len(masks) == (comb((1 << n)-1, 2) if n <= 7 else comb(n, 2))
    print(f"n={n}: |M|={len(points)+1}, lines={len(lines)}, "
          f"parity checks={len(masks)}, all even, nonadditive witness=(1,8,9)")
    if n == 5:
        keys = [(1 << i, 1 << j) for i, j in combinations(range(n), 2)]
        print("n=5 triples:", " ".join("/".join(map(str, T)) for T in lines))
        print("n=5 lexicographic N0:", *(concurrence(lines, u, v)[0] for u, v in keys))
    return lines


def main():
    lines = check(2)
    for m in (3, 4, 5):
        check(m)
    # Change the last coordinate on exactly two points of one line.
    # This keeps the projection and all line hypotheses, but not the parity.
    T = lines[0]
    bad = ((T[0] ^ 16, T[1] ^ 16, T[2]),) + lines[1:]
    assert len({x for U in bad for x in U}) == 15
    assert all(x ^ y ^ z == 0 for x, y, z in bad)
    items = [(i, j) for i, j in combinations(range(5), 2)
             if concurrence(bad, 1 << i, 1 << j)[0] % 2]
    assert items
    print("negative control: changed one lift, odd N0 coordinate pairs (0-based):", items)


if __name__ == "__main__":
    main()
