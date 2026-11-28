#!/usr/bin/env python3
"""Truth-table subcubes and disjoint-block witnesses, no run algorithm."""
from functools import lru_cache
from itertools import combinations


@lru_cache(None)
def masks(n, d):
    return [sum(1 << ((i-s) % n) for i in range(d)) for s in range(n)]


def value(x, n, d):
    return sum((x & w) == w for w in masks(n, d)) % 2


def cert_complexity(n, d):
    """Each bit of good[S] certifies a point x on a constant S-subcube."""
    N = 1 << n
    all_points = (1 << N)-1
    x0 = [((1 << (1 << i))-1)*(
        all_points//((1 << (2 << i))-1)) for i in range(n)]

    def shift(v, i):
        return ((v & x0[i]) << (1 << i)) | ((v & (all_points ^ x0[i])) >> (1 << i))

    f = int.from_bytes(bytes(sum(value(k+i, n, d) << i for i in range(8))
                             for k in range(0, N, 8)), "little")
    equal = [all_points ^ (f ^ shift(f, i)) for i in range(n)]
    good = {0: all_points}
    for size in range(1, n+1):
        current, cover = {}, 0
        for I in combinations(range(n), size):
            i = I[-1]
            S = sum(1 << j for j in I)
            small = good[S ^ (1 << i)]
            a = small & shift(small, i) & equal[i]
            current[S] = a
            cover |= a
        if cover != all_points:
            return n-size+1
        good = current
    return 0


def lower_witness(d, q, rho):
    n = q*(d+2)+rho
    h = d+2-rho
    deficit = min((rho+1)//2, h) if h <= q+1 else (rho+1)//2
    if h <= q+1 and h <= (rho+1)//2:
        word = ("1"*d+"0")*h + ("1"*d+"00")*(q+1-h)
        pairs = []
    else:
        t, r = divmod(rho, 2)
        word = "1"*(d+2*t)+"0"*(2+r)+("1"*d+"00")*(q-1)
        pairs = [(2*i+1, d+2*i) for i in range(t)]
    assert len(word) == n
    x = int(word[::-1], 2)
    f = value(x, n, d)
    singletons = [(i,) for i in range(n) if value(x ^ (1 << i), n, d) != f]
    blocks = singletons + pairs
    assert len(blocks) == n-deficit
    assert len({i for block in blocks for i in block}) == sum(map(len, blocks))
    for block in blocks:
        assert value(x ^ sum(1 << i for i in block), n, d) != f
    return len(blocks)


def main():
    certified = []
    for d, N in ((4, 14), (6, 14), (8, 17)):
        row = []
        for n in range(2*d-1, N+1):
            c = cert_complexity(n, d)
            q, rho = divmod(n, d+2)
            h = d+2-rho
            deficit = min((rho+1)//2, h) if h <= q+1 else (rho+1)//2
            assert c == n-deficit
            row.append(c)
        certified.append((d, tuple(row)))
    print(f"independent: exact small n certificate complexities {certified}")
    tests, blocks = 0, 0
    for d in range(4, 34, 2):
        for q in range(1, max(2, d//2-1)+2):
            for rho in range(d+2):
                if q*(d+2)+rho < 2*d-1:
                    continue
                blocks += lower_witness(d, q, rho)
                tests += 1
    assert certified[-1][-1][-1] == 13  # (d,n)=(8,17), not the large-length value 14.
    print(f"independent: {tests} lower witnesses and {blocks} disjoint sensitive blocks PASS")


if __name__ == "__main__":
    main()
