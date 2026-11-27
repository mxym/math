#!/usr/bin/env python3
"""Check all witnesses against the pinned seven-variable cubic catalogue (Python 3.10+)."""
import argparse
import csv
import hashlib
import re
from pathlib import Path
from urllib.request import urlopen

URL = "https://langevin.univ-tln.fr/project/agl7/data/B-0-3-7.dat"
HASH = "07ead6fb7809c4f249b3a6b6e4f895b5d1d43fbbc3606cccbe0c3bcb3fa75846"
SIZE = 776843
HERE = Path(__file__).resolve().parent
HEADER = ["orbit_index", "lower_half_hex"]


def check(condition, message):
    if not condition:
        raise ValueError(message)


def anf_table(poly):
    """Evaluate every monomial at every input, without using any orbit metadata."""
    if poly == "0":
        return 0
    terms = poly.split("+")
    check(len(terms) == len(set(terms)), f"duplicate monomial: {poly}")
    masks = []
    for term in terms:
        if term == "1":
            masks.append(0)
        else:
            check(re.fullmatch("[a-g]{1,3}", term) and
                  "".join(sorted(set(term))) == term, f"bad cubic term: {term}")
            masks.append(sum(1 << (ord(c) - ord("a")) for c in term))
    return sum((sum((x & m) == m for m in masks) % 2) << x for x in range(128))


def balanced_catalogue(raw):
    check(len(raw) == SIZE and hashlib.sha256(raw).hexdigest() == HASH,
          "source length or SHA-256 mismatch; do not silently substitute a new catalogue")
    polys = [line[4:] for line in raw.decode("ascii").splitlines() if line.startswith("anf=")]
    check(len(polys) == 3486, "expected 3486 ANFs")
    tables = [anf_table(p) for p in polys]
    check(len(set(tables)) == 3486, "catalogue contains repeated truth tables")
    result = {i: h for i, h in enumerate(tables) if h.bit_count() == 64}
    check(len(result) == 768, "expected 768 balanced representatives")
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--catalogue", type=Path, help="locally cached B-0-3-7.dat")
    g.add_argument("--download", action="store_true", help="read pinned public source into memory")
    p.add_argument("--certificates", type=Path, default=HERE / "certificates.tsv")
    args = p.parse_args()
    if args.download:
        with urlopen(URL, timeout=120) as f:
            raw = f.read(SIZE + 1)
    else:
        raw = args.catalogue.read_bytes()
    balanced = balanced_catalogue(raw)

    # Bit x of linear[u] is the inner product of x and u over F2.
    linear = [sum(((u & x).bit_count() % 2) << x for x in range(256)) for u in range(256)]
    seen = set()
    with args.certificates.open(encoding="ascii", newline="") as file:
        rows = csv.reader(file, delimiter="\t")
        check(next(rows, None) == HEADER, "unexpected TSV header")
        for n, row in enumerate(rows, 2):
            check(len(row) == 2 and row[0].isascii() and row[0].isdecimal() and
                  re.fullmatch("[0-9a-f]{32}", row[1]), f"malformed certificate line {n}")
            idx, v = int(row[0]), int(row[1], 16)
            check(idx in balanced and idx not in seen, f"unexpected/repeated orbit {idx}")
            seen.add(idx)
            h = balanced[idx]
            f = v | ((v ^ h) << 128)
            for x in range(256):
                check((((f >> x) ^ (f >> (x ^ 128)) ^ (h >> (x & 127))) & 1) == 0,
                      f"incorrect derivative for orbit {idx}, input {x}")
            for u, character in enumerate(linear):
                w = 256 - 2 * (f ^ character).bit_count()
                check(abs(w) == 16, f"non-bent witness for orbit {idx}, character {u}: {w}")
    check(seen == set(balanced), f"missing orbits: {sorted(balanced.keys() - seen)}")
    print("verified pinned catalogue: 3486 cubic-or-lower AGL representatives")
    print("balanced representatives: 768; witnesses: 768")
    print("derivative identities checked: 196608; Walsh coefficients checked: 196608 (all +/-16)")


if __name__ == "__main__":
    main()
