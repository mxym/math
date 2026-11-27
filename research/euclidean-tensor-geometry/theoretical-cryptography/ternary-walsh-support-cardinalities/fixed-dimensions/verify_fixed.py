#!/usr/bin/env python3
"""Independent modular Fourier audit of all fixed-dimension witnesses."""
from collections import Counter
from hashlib import sha256
import json
import gzip
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "witnesses-fixed.json.gz"
RAW = gzip.decompress(ARCHIVE.read_bytes())
DATA = json.loads(RAW)
P = 65521
ROOTS = (16673, 48847)
FORBIDDEN = {2, 4, 5, 8, 10, 11}


def require(flag, msg):
    if not flag:
        raise AssertionError(msg)


def transform_mod(word, root):
    """Tensor DFT using x0+x1*r^{-u}+x2*r^{-2u}, in-place by axes."""
    a = [pow(root, int(ch), P) for ch in word]
    step = 1
    r2 = root * root % P
    while step < len(a):
        for off in range(0, len(a), 3 * step):
            for j in range(step):
                i = off + j
                x, y, z = a[i], a[i + step], a[i + 2 * step]
                a[i] = (x + y + z) % P
                a[i + step] = (x + r2*y + root*z) % P
                a[i + 2*step] = (x + root*y + r2*z) % P
        step *= 3
    return a


def support(word):
    require(set(word) <= set("012"), "nonternary truth table")
    n = len(word)
    m = 1
    while m < n:
        m *= 3
    require(m == n, "truth-table length is not a power of three")
    a, b = (transform_mod(word, r) for r in ROOTS)
    # The two roots are distinct roots of X^2+X+1 over F_P.  A true
    # Eisenstein coefficient has integer coordinates of absolute value <=n<P;
    # both projections vanish iff both coordinates are exactly zero.
    require(all((x == 0) == (y == 0) for x, y in zip(a, b)),
            "the two exact projections disagree on a zero")
    return sum(x != 0 for x in a)


def direct_bins(word):
    """Slow independent residue-histogram transform, used on pair controls."""
    n = len(word)
    d = 0
    while 3 ** d < n:
        d += 1
    coords = [tuple((i // (3 ** j)) % 3 for j in range(d)) for i in range(n)]
    out = []
    for u in coords:
        bins = [0, 0, 0]
        for x, ch in zip(coords, word):
            bins[(int(ch) - sum(a*b for a, b in zip(x, u))) % 3] += 1
        out.append((bins[0]-bins[2], bins[1]-bins[2]))
    return out


def rotate(z, k):
    a, b = z
    return ((a,b), (-b,a-b), (b-a,-a))[k % 3]


def pair_count(g, h):
    G, H = direct_bins(g), direct_bins(h)
    return sum((a[0] + rotate(b, -t)[0] != 0 or
                a[1] + rotate(b, -t)[1] != 0)
               for a, b in zip(G, H) for t in range(3))


def main():
    require(pow(ROOTS[0], 2, P) + ROOTS[0] + 1 == P, "bad first root")
    require(pow(ROOTS[1], 2, P) + ROOTS[1] + 1 == P, "bad second root")
    require(ROOTS[0] != ROOTS[1], "roots coincide")
    W = DATA["witnesses"]
    lines = []
    for n in range(3, 8):
        table = W[str(n)]
        if n >= 4:
            expect = set(range(1, 3**n + 1)) - FORBIDDEN
            require(set(map(int, table)) == expect, f"n={n}: wrong target keys")
        hist = Counter()
        for key, word in table.items():
            require(len(word) == 3**n, f"n={n} size={key}: wrong length")
            got = support(word)
            require(got == int(key), f"n={n} size={key}: got {got}")
            hist[got] += 1
        raw = json.dumps(table, separators=(",", ":")).encode()
        digest = sha256(raw).hexdigest()
        lines.append(f"n={n}: {len(table)} witnesses, range 1..{3**n}, sha256 {digest}")

    pairs = {
        9: ("000111000", "000000000"),
        22:("020100000", "021000000"),
        26:("020211000", "001200000"),
    }
    for q, pair in pairs.items():
        require(pair_count(*pair) == q, f"bad bridge pair q={q}")
    # Consequence of the fixed witnesses and the already-proved six global
    # exclusions: minimum positive dimension through 3^7.
    first = {}
    for n in range(1, 8):
        available = ({1,3} if n == 1 else
                     {1,3,6,7,9} if n == 2 else
                     set(map(int, W[str(n)])))
        for s in available:
            first.setdefault(s, n)
    for s in range(1, 3**7 + 1):
        if s in FORBIDDEN:
            continue
        ceil_log = 1
        while 3**ceil_log < s:
            ceil_log += 1
        require(first[s] == max(1, ceil_log), f"bad minimum dimension at {s}")

    print("\n".join(lines))
    print("witness json bytes/sha256:", len(RAW), sha256(RAW).hexdigest())
    print("bridge pair counts:", " ".join(f"q={q}" for q in pairs))
    print("minimum positive dimensions verified for every attainable size <=2187")


if __name__ == "__main__":
    main()
