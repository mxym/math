#!/usr/bin/env python3
"""Independent parity-mask dot products and autocorrelation-idempotence checker."""
import csv
import hashlib
import json
import re
from pathlib import Path
import sys
from collections import Counter
from zipfile import ZipFile

CATALOGUE = "6f1d7c7012d987d2d75a9618dd569959e66928d573c5f9b43db0b4276bcdecf8"
NIST = "dad0e32432a48483f00b399a2432316e5d717ad464fca8810dec8f64cc467b6e"
PROFILE_DIGEST = "c095da574e982826dfe333b6a2ad0b11480f001d42606b6da62b248dbfd7ad2d"


def masks(length):
    return [sum(1 << x for x in range(length) if (u & x).bit_count() & 1)
            for u in range(length)]


def spectrum(function, characters):
    length = len(characters)
    return [length - 2 * (function ^ chi).bit_count() for chi in characters]


def autocorr(function):
    sign = [(-1) ** ((function >> x) & 1) for x in range(128)]
    return [sum(sign[x] * sign[x ^ d] for x in range(128)) for d in range(128)]


def check_idempotence(a, amplitude):
    return all(sum(a[x] * a[x ^ y] for x in range(128)) == amplitude * amplitude * a[y]
               for y in range(128))


def nist_reps(path):
    blob = path.read_bytes()
    assert hashlib.sha256(blob).hexdigest() == NIST
    lines = iter(line for line in blob.splitlines() if line.strip())
    out = []
    for i in range(30883):
        match = re.fullmatch(rb"group (\d+) size (\d+)(?: .*)?", next(lines))
        assert match and int(match[1]) == i and int(match[2]) > 0
        for _ in range(int(match[2])):
            row = next(lines)
            assert re.fullmatch(rb"[0-9a-f]{16}", row)
            out.append(int(row, 16))
    assert next(lines, None) is None
    assert len(out) == len(set(out)) == 150357
    return out


def main(path, nist_path=None):
    assert hashlib.sha256(path.read_bytes()).hexdigest() == CATALOGUE
    with Path(__file__).with_name("witnesses.tsv").open(encoding="ascii", newline="") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    htable = {int(row["class_id"]): int(row["h_hex"], 16) for row in rows}
    assert len(htable) == len(rows) == 558
    assert all(0 <= h < 1 << 64 for h in htable.values())
    ftable = {}
    with ZipFile(path) as z:
        for info in z.infolist():
            assert not info.is_dir()
            for row in z.read(info.filename).splitlines():
                if not row.strip():
                    continue
                cls, tt, end = row.split(b";")
                assert not end and cls.startswith(b"class=") and tt.startswith(b" tt=")
                i = int(cls[6:])
                lo, hi = tt[4:].split(b",")
                assert i not in ftable
                ftable[i] = int.from_bytes(int(lo, 16).to_bytes(4, "little")
                                          + int(hi, 16).to_bytes(4, "little"), "little")
    assert set(ftable) == set(range(1, 150_358))
    chis6, chis7 = masks(64), masks(128)
    count = Counter()
    matched = set()
    digest = hashlib.sha256()
    profiles = Counter()
    for i, f in sorted(ftable.items()):
        pp = tuple(sorted(map(abs, spectrum(f, chis6))))
        profiles[pp] += 1
        sf = set(pp) - {0}
        if len(sf) == 1:
            count[next(iter(sf))] += 1
        elif sf in ({8, 16}, {16, 32}):
            h = htable[i]
            wf = f + (h << 64)
            a, b = sorted(sf)
            mult = Counter(map(abs, spectrum(wf, chis7)))
            assert mult == {0: 128 - 128**2 // b**2, b: 128**2 // b**2}, i
            assert check_idempotence(autocorr(wf), b), i
            matched.add(i)
            count[a, b] += 1
            digest.update(f"{i}\t{f:016x}\t{h:016x}\t{a}\t{b}\n".encode("ascii"))
            if i == 1326:  # An explicit one-bit mutation cannot remain plateaued at b.
                assert not check_idempotence(autocorr(wf ^ (1 << 64)), b)
    assert matched == set(htable)
    assert count == {8: 4, 16: 5, 32: 1, 64: 1, (8, 16): 556, (16, 32): 2}
    pd = hashlib.sha256(json.dumps(sorted(profiles.items()), separators=(",", ":")).encode()).hexdigest()
    assert len(profiles) == 2082 and pd == PROFILE_DIGEST
    if nist_path is not None:
        rr = nist_reps(nist_path)
        assert len(set(rr).intersection(ftable.values())) == 1
        nist_profiles = Counter(tuple(sorted(map(abs, spectrum(f, chis6)))) for f in rr)
        assert nist_profiles == profiles
        print(f"Fuller vs NIST: all absolute-Walsh multiset counts agree ({len(profiles)} profiles).")
    print("Full catalogue absolute-Walsh profile digest:", pd)
    print("Independent direct counts:", count)
    print("Mixed witness (id,f,h,a,2a) digest:", digest.hexdigest())
    print("PASS: 150357 direct spectra, 558 direct 128-point spectra and AC identities; mutant rejected")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Do not run with Python -O.")
    if len(sys.argv) not in (2,3):
        raise SystemExit("Usage: python3 verify_direct.py n6-classes.zip [n6_group_data.txt]")
    main(*map(Path, sys.argv[1:]))
