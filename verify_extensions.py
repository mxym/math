"""Check explicit extensions of all GLP abnormal representatives; Python 3.10+."""
import argparse
import csv
import hashlib
import re
from collections import Counter
from pathlib import Path
from urllib.request import urlopen

BASE = "https://langevin.univ-tln.fr/project/indice/"
REPS = ("representatives.txt", 143577, "f276d07eedeee1a8db90e0f453317d36ae420a168eb739a255d726eff5f1aa79")
LIST = ("ab-near-expandable.txt", 11128, "2fd116635d8e67113fc7f12ea7e0dc6545291e0220a54b644ac93ae3f6d57dae")
HERE = Path(__file__).resolve().parent


def check(ok, msg):
    if not ok:
        raise ValueError(msg)


def load(spec, path):
    name, size, digest = spec
    if path is None:
        with urlopen(BASE + name, timeout=120) as f:
            data = f.read(size + 1)
    else:
        data = path.read_bytes()
    check(len(data) == size and hashlib.sha256(data).hexdigest() == digest, f"source changed: {name}")
    return data.decode("ascii").splitlines()


def truth(poly):
    terms = poly.split("+")
    masks = []
    for term in terms:
        check(re.fullmatch("[a-g]{1,4}", term) and term == "".join(sorted(set(term))),
              f"invalid representative monomial: {term}")
        masks.append(sum(1 << (ord(a)-97) for a in term))
    return sum((sum((x & m) == m for m in masks) % 2) << x for x in range(128))


def walsh(f, n):
    v = [1 - 2 * ((f >> x) & 1) for x in range(1 << n)]
    step = 1
    while step < len(v):
        for start in range(0, len(v), 2 * step):
            for j in range(start, start + step):
                a, b = v[j], v[j+step]
                v[j], v[j+step] = a+b, a-b
        step *= 2
    return v


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--download", action="store_true")
    p.add_argument("--representatives", type=Path)
    p.add_argument("--published-30", type=Path, dest="smaller")
    p.add_argument("--certificates", type=Path, default=HERE/"extensions.tsv")
    args = p.parse_args()
    if args.download:
        if args.representatives or args.smaller:
            p.error("choose downloads or both local files")
    elif not (args.representatives and args.smaller):
        p.error("supply --download, or both --representatives and --published-30")
    reps = [l[4:] for l in load(REPS, args.representatives) if l.startswith("anf=")]
    small = [l[4:].split()[0].removeprefix("1+") for l in load(LIST, args.smaller)
             if l.startswith("anf=") and "(" in l]
    check(len(reps) == len(set(reps)) == 1309 and len(small) == len(set(small)) == 30,
          "unexpected source record count")
    check(set(small) <= set(reps), "published subset not recognized")
    check(reps[5] not in small, "specified example is in the 30")
    seen = set()
    with args.certificates.open(encoding="ascii", newline="") as f:
        rows = csv.reader(f, delimiter="\t")
        check(next(rows, None) == ["i", "q"], "unexpected header")
        for row in rows:
            check(len(row) == 2 and row[0].isdecimal() and re.fullmatch("[0-9a-f]{32}",row[1]),
                  "malformed witness")
            i = int(row[0])
            check(0 <= i < len(reps) and i not in seen, "bad/duplicate index")
            seen.add(i)
            lo, hi = truth(reps[i]), int(row[1], 16)
            check(set(walsh(lo, 7)) == {0, 16, -16}, f"source is not near-bent at index {i}")
            w = walsh(lo | (hi << 128), 8)
            check(set(w) == {16, -16}, f"non-bent extension at index {i}")
            if i == 5:
                print(f"example i=5: lower={lo:032x} upper={hi:032x}; Walsh histogram={dict(Counter(w))}")
    check(seen == set(range(1309)), "coverage incomplete")
    print("verified all 1309 extensions (335104 full Walsh coefficients)")
    print("published comparison list: 30 source indices; additional indices with certified extensions: 1279")


if __name__ == "__main__":
    main()
