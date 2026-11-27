#!/usr/bin/env python3
"""Exact ternary Fourier witnesses and ascending construction, no dependencies."""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DAT = json.loads((ROOT / "witnesses.json").read_text())
SMALL, BAND, PAIRS = ({int(k): v for k, v in DAT[z].items()}
                      for z in ("small", "band", "pairs"))
POWERS = ((1, 0), (0, 1), (-1, -1))


def require(flag, text):
    if not flag:
        raise ValueError(text)


def words(n):
    return ["".join(map(str, z)) for z in product(range(3), repeat=n)]


def coordinates(n):
    return [tuple(map(int, reversed(z))) for z in words(n)]


def dimension(tt):
    N = len(tt)
    d = 0
    while N > 1 and N % 3 == 0:
        N //= 3
        d += 1
    require(N == 1 and all(x in "012" for x in tt), "bad truth table")
    return d


def bins(tt):
    xyz = coordinates(dimension(tt))
    g = list(map(int, tt))
    ans = []
    for u in xyz:
        h = [0, 0, 0]
        for x, a in zip(xyz, g):
            h[(a-sum(e*f for e, f in zip(x, u))) % 3] += 1
        ans.append(tuple(h))
    return ans


def ring_of_bins(H):
    return [(a-c, b-c) for a, b, c in H]


def rot(z, p):
    a, b = z
    return ((a, b), (-b, a-b), (b-a, -a))[p]


def fft(tt):
    A = [POWERS[int(x)] for x in tt]
    h = 1
    while h < len(A):
        for offset in range(0, len(A), 3*h):
            for i in range(offset, offset+h):
                z, u, v = A[i], A[i+h], A[i+2*h]
                for j in range(3):
                    b, c = rot(u, (-j) % 3), rot(v, j)
                    A[i+j*h] = (z[0]+b[0]+c[0], z[1]+b[1]+c[1])
        h *= 3
    return A


def support(A):
    return [j for j, x in enumerate(A) if x != (0, 0)]


def checked(tt):
    W = fft(tt)
    require(W == ring_of_bins(bins(tt)), "FFT and direct histogram disagreed")
    return support(W)


def q_of(g, h):
    G, H = bins(g), bins(h)
    r = 0
    for a, b in zip(G, H):
        for t in range(3):
            c = [a[i] + b[(i+t) % 3] for i in range(3)]
            r += len(set(c)) != 1
    return r


def compose(f, g, h):
    d = max(map(dimension, (f, g, h)))
    f, g, h = (t * (3**d // len(t)) for t in (f, g, h))
    # Coordinates are x followed by fresh y, then fresh selector t.
    return "".join(str((int(x)+y) % 3) for y in range(3) for x in f) + 3*g + 3*h


def constructor(r, trace=None):
    if r in SMALL:
        return SMALL[r]
    if r in BAND:
        return BAND[r]
    if r >= 58:
        q = (3, 16, 14)[r % 3]
    elif 28 <= r <= 57:
        q = next(q for q in sorted(PAIRS) if (r-q) % 3 == 0 and (r-q)//3 in SMALL.keys()|BAND.keys())
    else:
        raise ValueError("inadmissible support size")
    s = (r-q)//3
    require(1 <= s < r and 3*s+q == r, "bad recurrence step")
    if trace is not None:
        trace.append((r, s, q))
    return compose(constructor(s, trace), *PAIRS[q])


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("--construct", type=int, help="display a truth table of the requested size")
    args = cli.parse_args()
    if args.construct is not None:
        tr = []
        tt = constructor(args.construct, tr)
        require(len(support(fft(tt))) == args.construct, "constructed table had the wrong size")
        print("n =", dimension(tt), "size =", args.construct, "steps =", tr)
        print(tt)
        return

    for n in (1, 2):
        H = Counter()
        geom6 = 0
        for tt in words(3**n):
            S = checked(tt)
            H[len(S)] += 1
            if len(S) == 6:
                removed = set(range(9)) - set(S)
                require(sum(x % 3 for x in removed) % 3 == sum(x // 3 for x in removed) % 3 == 0,
                        "size-six complement is not collinear")
                geom6 += 1
        expect = {1: 9, 3: 18} if n == 1 else {1: 27, 3: 216, 6: 1944, 7: 3888, 9: 13608}
        require(H == expect, "unexpected small-dimensional census")
        print(f"n={n} full census {dict(sorted(H.items()))}; size-6 lines checked={geom6}.")
    for r, f in (SMALL | BAND).items():
        require(len(checked(f)) == r, f"bad table for size {r}")
    for q, (g, h) in PAIRS.items():
        require(q_of(g, h) == q, f"bad two-leaf count {q}")
    print("PASS 21 exact truth tables and 8 two-leaf counts.")
    for r in range(28, 58):
        require(len(checked(constructor(r))) == r, f"bad bridging construction {r}")
    for r in (58, 59, 60, 73, 90, 100, 123):
        require(len(support(fft(constructor(r)))) == r, f"bad recursive construction {r}")
    print("PASS all 30 bridging sizes and seven deeper construction checks.")
    # A perturbation of an affine table has all nine frequencies, not one.
    require(len(checked("100000000")) != 1, "mutated size-one witness wrongly accepted")
    require(q_of(PAIRS[14][0], PAIRS[14][0]) != 14, "duplicated pair wrongly accepted")
    print("PASS witness negative controls.")


if __name__ == "__main__":
    main()
