"""Independent certificate check via finite differences, plus abnormality and EA tests.
Usage: python3 verify_independent.py REPRESENTATIVES.txt PUBLISHED-30.txt [extensions.tsv]
No imports from the first verifier, no FWHT, and a different ANF-to-table procedure.
"""
import hashlib
from itertools import combinations
from pathlib import Path
import sys


def require(condition, msg):
    if not condition:
        raise ValueError(msg)


def read_pinned(path, digest):
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == digest, f"source SHA mismatch: {path}")
    return data.decode("ascii").splitlines()


def anf_zeta(s):
    """Truth values by the Boolean subset zeta transform of ANF coefficients."""
    a = [0] * 128
    for term in s.split("+"):
        idx = 0
        for c in term:
            if c != "1":
                idx |= 1 << "abcdefg".index(c)
        a[idx] ^= 1
    for j in range(7):
        e = 1 << j
        for x in range(128):
            if x & e:
                a[x] ^= a[x ^ e]
    return sum(bit << x for x, bit in enumerate(a))


def translates(f, n):
    """All tables x -> f(x XOR d), in increasing d, by swapping half-blocks."""
    tables = [f]
    for b in range(n):
        step = 1 << b
        lower = sum((1 << x) for x in range(1 << n) if not x & step)
        tables += [((z & lower) << step) | ((z >> step) & lower) for z in tables]
    return tables


def ea_invariant(f):
    # D_d(f circ A + l) = (D_{Ad} f) circ A + constant; translation is included.
    # Each absolute Walsh spectrum is permuted, and the directions themselves permute.
    linear = [sum((((x & u).bit_count() & 1) << x) for x in range(128)) for u in range(128)]
    profiles = []
    for tr in translates(f, 7)[1:]:
        der = f ^ tr
        profiles.append(tuple(sorted(abs(128 - 2*(der ^ lin).bit_count()) for lin in linear)))
    return tuple(sorted(profiles))


def abnormality_check(f):
    all_inputs = range(128)
    # Each of the 32 truth tables below is an affine Boolean function of four bits.
    affine = {sum(((((m & i).bit_count() + c) & 1) << i) for i in range(16))
              for m in range(16) for c in range(2)}
    require(len(affine) == 32, "internal affine table count")
    count = 0
    for piv in combinations(range(7), 4):
        free = [(r, j) for r in range(4) for j in range(piv[r]+1, 7) if j not in piv]
        pivmask = sum(1 << j for j in piv)
        cosets = [x for x in all_inputs if not x & pivmask]
        for pat in range(1 << len(free)):
            basis = [1 << j for j in piv]
            for k, (r, j) in enumerate(free):
                if pat >> k & 1:
                    basis[r] |= 1 << j
            span = [0]
            for d in basis:
                span += [y ^ d for y in span]
            for a in cosets:
                restricted = sum(((f >> (a^y)) & 1) << k for k,y in enumerate(span))
                require(restricted not in affine, "an affine restriction exists")
                count += 1
    require(count == 94488, "incorrect number of affine four-flats")
    return count


def main():
    if len(sys.argv) not in (3, 4):
        raise SystemExit(__doc__)
    reps_path, small_path = map(Path, sys.argv[1:3])
    cert = Path(sys.argv[3]) if len(sys.argv) == 4 else Path(__file__).with_name("extensions.tsv")
    reps = [s[4:] for s in read_pinned(reps_path, "f276d07eedeee1a8db90e0f453317d36ae420a168eb739a255d726eff5f1aa79")
            if s.startswith("anf=")]
    smaller = [anf_zeta(s[4:].split()[0]) for s in read_pinned(small_path, "2fd116635d8e67113fc7f12ea7e0dc6545291e0220a54b644ac93ae3f6d57dae")
               if s.startswith("anf=") and "(" in s]
    require(len(reps) == 1309 and len(set(smaller)) == 30, "bad source record counts")
    # Cross-reference the 30 literal Sage hex tables in arXiv:2504.21779v1, App. A Listing A.1.
    # Digest convention: sort 32-digit lowercase words lexicographically; LF after every word.
    data = "".join(f"{f:032x}\n" for f in sorted(smaller)).encode("ascii")
    require(hashlib.sha256(data).hexdigest() == "73fe98de02fd5fbfbb07bd7e4b82c3b502ec8c0b578ae19defbbf362b244c0a5",
            "source companion doesn't reproduce the 30 printed hex tables")
    rows = cert.read_text(encoding="ascii").splitlines()
    require(len(rows) == 1310 and rows[0] == "i\tq", "incomplete certificates")
    for i, (poly, row) in enumerate(zip(reps, rows[1:])):
        index, upper = row.split("\t")
        require(int(index) == i and len(upper) == 32, f"bad row order or size at {i}")
        low = anf_zeta(poly)
        g = low | (int(upper, 16) << 128)
        for d, shifted in enumerate(translates(g, 8)[1:], 1):
            require((g ^ shifted).bit_count() == 128, f"unbalanced derivative: {i=}, {d=}")
        if i == 12:
            print(f"example i=12: lower {low:032x}, upper {upper}")
    print("independently verified all 333795 nonzero-direction difference weights (each exactly 128)")
    extra = anf_zeta(reps[12])
    e = ea_invariant(extra)
    require(all(ea_invariant(s) != e for s in smaller), "invariant failed to separate selected example")
    print("index 12 EA-invariant differs from all 30 appendix entries")
    n = abnormality_check(extra)
    print(f"index 12 has no affine restrictions on its {n} affine four-flats")


if __name__ == "__main__":
    main()
