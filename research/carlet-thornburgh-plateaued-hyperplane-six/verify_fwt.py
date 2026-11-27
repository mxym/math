#!/usr/bin/env python3
"""Check every catalogue row and every extension by integer butterfly transforms."""
import argparse
from collections import Counter
from hashlib import sha256
from pathlib import Path
import re
import zipfile

ZIP_HASH = "6f1d7c7012d987d2d75a9618dd569959e66928d573c5f9b43db0b4276bcdecf8"
N = 64
NC = 150357
MIXED = {(8, 16), (16, 32)}
MIXED_HIST = {
    (8, 16, 4): 8, (8, 16, 6): 49, (8, 16, 7): 81,
    (8, 16, 8): 214, (8, 16, 9): 103, (8, 16, 10): 83,
    (8, 16, 12): 18, (16, 32, 1): 1, (16, 32, 2): 1,
}
PLATEAUED = {8: 4, 16: 5, 32: 1, 64: 1}


def walsh(word, length):
    w = [1 - 2 * ((word >> i) & 1) for i in range(length)]
    step = 1
    while step < length:
        for base in range(0, length, 2 * step):
            for j in range(base, base + step):
                a, b = w[j], w[j + step]
                w[j], w[j + step] = a + b, a - b
        step *= 2
    return w


def nonzero_abs(w):
    return tuple(sorted(set(map(abs, w)) - {0}))


def parse_archive(path):
    assert sha256(path.read_bytes()).hexdigest() == ZIP_HASH, "catalogue byte hash"
    entry = re.compile(r"class=\s*(\d+); tt=(0x[0-9A-F]{8}),(0x[0-9A-F]{8});")
    name = re.compile(r"n6_nl(\d+)_ord(\d+)_acmax(\d+)\.exp")
    out = {}
    with zipfile.ZipFile(path) as z:
        assert len(z.namelist()) == 182 == len(set(z.namelist()))
        for f in z.namelist():
            nn = name.fullmatch(f)
            assert nn, f
            nl = int(nn[1])
            for line in z.read(f).decode("ascii").splitlines():
                if not line.strip():
                    continue
                m = entry.fullmatch(line)
                assert m, (f, line)
                i = int(m[1])
                assert i not in out, i
                out[i] = (int(m[2], 16) | (int(m[3], 16) << 32), nl)
    assert set(out) == set(range(1, NC + 1))
    return out


def parse_witnesses():
    path = Path(__file__).with_name("witnesses.tsv")
    header, *lines = path.read_text(encoding="ascii").splitlines()
    assert header == "class_id\th_hex"
    out = {}
    for line in lines:
        i, h = line.split("\t")
        assert re.fullmatch(r"[1-9]\d*", i)
        assert re.fullmatch(r"[0-9a-f]{16}", h)
        i = int(i)
        assert i not in out and (not out or next(reversed(out)) < i)
        out[i] = int(h, 16)
    assert len(out) == 558
    return out


def check_moments(wf, wh, a, calibrated=True):
    assert all((x - y) % (2 * a) == 0 for x, y in zip(wh, wf))
    v = [(x - y) // (2 * a) for x, y in zip(wh, wf)]
    p = N // a
    for mask in range(N):
        modulus = p >> mask.bit_count()
        if modulus > 1:
            j = (sum(t for i, t in enumerate(v) if i & mask == mask) % modulus)
            if j:
                if not calibrated:
                    return False
                raise AssertionError((mask, modulus, j))
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalogue", type=Path)
    path = parser.parse_args().catalogue
    reps = parse_archive(path)
    cert = parse_witnesses()
    plateaued = Counter()
    mixed_hist = Counter()
    visited = set()
    digest = sha256()
    for i in range(1, NC + 1):
        f, nl = reps[i]
        wf = walsh(f, N)
        profile = nonzero_abs(wf)
        assert sum(t * t for t in wf) == N * N
        assert nl == (N - profile[-1]) // 2
        if len(profile) == 1:
            plateaued[profile[0]] += 1
            continue
        if profile not in MIXED:
            assert profile != (32, 64), i
            continue
        a, amp = profile
        assert i in cert, ("missing certificate", i)
        h = cert[i]
        wh = walsh(h, N)
        wg = walsh(f | (h << N), 2 * N)
        assert set(map(abs, wg)) == {0, amp}, i
        assert wg == [u + v for u, v in zip(wf, wh)] + [u - v for u, v in zip(wf, wh)]
        xcount = sum(abs(t) == amp for t in wf)
        assert sum(abs(t) == amp for t in wh) == xcount
        for u, v in zip(wf, wh):
            assert (
                (abs(u) == amp and v == 0)
                or (abs(u) == a and abs(v) == a)
                or (u == 0 and abs(v) in (0, amp))
            ), i
        assert check_moments(wf, wh, a)
        mixed_hist[a, amp, xcount] += 1
        visited.add(i)
        digest.update(f"{i}\t{f:016x}\t{h:016x}\t{a}\t{amp}\n".encode("ascii"))

        if i == 1326:  # Exercise two different mistaken witnesses.
            assert set(map(abs, walsh(f | ((h ^ 1) << N), 2 * N))) != {0, amp}
            j = next(j for j in range(N) if abs(wh[j]) == a)
            wrong = wh[:]
            wrong[j] = -wrong[j]
            assert not check_moments(wf, wrong, a, calibrated=False)
    assert visited == set(cert)
    assert plateaued == PLATEAUED
    assert mixed_hist == MIXED_HIST
    print(f"Fuller EA IDs: 1..{NC} (182 files; SHA-256 locked)")
    print("Plateaued counts by amplitude:", dict(sorted(plateaued.items())))
    print("Mixed counts by (a, 2a, number of high coefficients):")
    for key, count in sorted(mixed_hist.items()):
        print(f"  {key}: {count}")
    print("Mixed witness (id,f,h,a,2a) digest:", digest.hexdigest())
    print("PASS: 558 mixed certificates, 11 plateaued, 569 in class 5; both negative controls rejected")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Do not run with Python -O.")
    main()
