#!/usr/bin/env python3
"""Replay the complete 120-extension and closed-orbit certificates.

Standard library only. Uses binary adjacency rows and Gaussian elimination.
Assertions are not used, so python -O does not disable any verification.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def graph(value: object, n: int) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == n, "invalid graph length")
    a = tuple(value)
    require(all(type(x) is int and 0 <= x < 1 << n for x in a), "invalid adjacency row")
    require(all(not (a[i] >> i & 1) for i in range(n)), "loop")
    require(all((a[i] >> j & 1) == (a[j] >> i & 1) for i in range(n) for j in range(n)), "asymmetry")
    return a


def fixed_representatives() -> dict[int, tuple[int, ...]]:
    return {1: (0,), 2: (2, 1), 3: (2, 5, 2), 4: (2, 5, 10, 4),
            5: (18, 5, 10, 20, 9), 6: (50, 37, 42, 52, 41, 31)}


def local_complement(a: tuple[int, ...], v: int) -> tuple[int, ...]:
    require(type(v) is int and 0 <= v < len(a), "invalid LC vertex")
    return tuple(row ^ ((a[v] ^ (1 << i)) if a[v] >> i & 1 else 0)
                 for i, row in enumerate(a))


def is_claw(a: tuple[int, ...], labels: object) -> bool:
    if not isinstance(labels, list) or len(labels) != 4:
        return False
    if not all(type(v) is int and 0 <= v < len(a) for v in labels) or len(set(labels)) != 4:
        return False
    c, *leaves = labels
    return all(a[c] >> v & 1 for v in leaves) and all(not (a[u] >> v & 1) for u, v in combinations(leaves, 2))


def has_claw(a: tuple[int, ...]) -> bool:
    return any(is_claw(a, [c, *leaves]) for c in range(len(a))
               for leaves in combinations([v for v in range(len(a)) if a[c] >> v & 1], 3))


def cut_rank(a: tuple[int, ...], subset: int) -> int:
    outside = ((1 << len(a)) - 1) ^ subset
    basis: dict[int, int] = {}
    for i, row in enumerate(a):
        if not (subset >> i & 1):
            continue
        x = row & outside
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return len(basis)


def expected_i3(n: int, sizes: list[int]) -> int:
    if min(sizes) == 0:
        return 0
    if n in (4, 5):
        return -1
    if n == 6 and sorted(sizes) == [1, 1, 2, 2]:
        return -2
    return 0


def verify(cert: dict) -> dict:
    require(cert.get("format") == "lc-claw-free-extensions-v1", "unsupported certificate format")
    reps = fixed_representatives()
    require(set(cert["representatives"]) == {str(n) for n in reps}, "missing representative")
    for n, rep in reps.items():
        require(graph(cert["representatives"][str(n)], n) == rep, "wrong fixed representative")
    records = cert["extensions"]
    require(isinstance(records, list), "extensions must be a list")
    expected = {(n, mask) for n in reps for mask in range(1, 1 << n)}
    observed = set()
    outcomes: Counter[str] = Counter()
    by_order = {n: Counter() for n in reps}
    max_lc = 0
    for record in records:
        n, mask = record["base_order"], record["attachment"]
        require(type(n) is int and type(mask) is int and (n, mask) in expected, "invalid extension index")
        require((n, mask) not in observed, "duplicate extension")
        observed.add((n, mask))
        a = reps[n] + (mask,)
        a = tuple(a[i] | ((((mask >> i) & 1) << n) if i < n else 0) for i in range(n+1))
        steps = record["lc"]
        require(isinstance(steps, list), "LC witness must be a list")
        max_lc = max(max_lc, len(steps))
        for v in steps:
            a = local_complement(a, v)
        if record["kind"] == "claw":
            require(is_claw(a, record["claw"]), f"false claw witness at {(n, mask)}")
        elif record["kind"] == "representative":
            require(n < 6, "forbidden seventh representative")
            order = record["order"]
            require(isinstance(order, list) and all(type(x) is int for x in order)
                    and sorted(order) == list(range(n+1)), "invalid isomorphism")
            target = reps[n+1]
            require(all((a[order[i]] >> order[j] & 1) == (target[i] >> j & 1)
                        for i in range(n+1) for j in range(n+1)), f"false isomorphism at {(n, mask)}")
        else:
            raise ValueError("unknown endpoint kind")
        outcomes[record["kind"]] += 1
        by_order[n][record["kind"]] += 1
    require(observed == expected, "incomplete extension coverage")
    require(max_lc <= 3, "three-step certificate bound failed")

    orbit_sizes = {}
    closure_checks = 0
    require(set(cert["closed_claw_free_orbits"]) == {str(n) for n in reps}, "missing orbit")
    for n, rep in reps.items():
        orbit_list = cert["closed_claw_free_orbits"][str(n)]
        orbit = {graph(x, n) for x in orbit_list}
        require(len(orbit) == len(orbit_list), "duplicate orbit member")
        require(rep in orbit, "root not in closed set")
        for a in orbit:
            require(not has_claw(a), "claw in a negative orbit certificate")
            for v in range(n):
                require(local_complement(a, v) in orbit, "set is not LC-closed")
                closure_checks += 1
        orbit_sizes[n] = len(orbit)

    entropy_histograms = {}
    entropy_cases = 0
    for n, rep in reps.items():
        entropy = [cut_rank(rep, s) for s in range(1 << n)]
        require(all(entropy[s] == entropy[((1 << n)-1)^s] for s in range(1 << n)), "cut-rank asymmetry")
        if n in (5, 6):
            require(all(entropy[s] == min(s.bit_count(), n-s.bit_count()) for s in range(1 << n)), "perfect cut-rank profile failed")
        if n == 4:
            require(sorted(entropy[s] for s in range(1 << n) if s.bit_count()==2) == [1,1,2,2,2,2], "P4 cut profile failed")
        hist: Counter[int] = Counter()
        for labels in product(range(4), repeat=n):
            blocks = [sum(1 << v for v in range(n) if labels[v]==j) for j in range(4)]
            a,b,c,d = blocks
            # For a pure state S(ABC)=S(D). This is the original tripartite information.
            i3 = sum(entropy[s] for s in blocks) - entropy[a|b] - entropy[a|c] - entropy[a|d]
            require(i3 == expected_i3(n, [s.bit_count() for s in blocks]), "incorrect all-partition entropy formula")
            require(i3 <= 0, "MMI violation in a negative representative")
            hist[i3] += 1
            entropy_cases += 1
        entropy_histograms[n] = dict(sorted(hist.items()))
    return {"status": "PASS", "checker": "bitmask-gaussian-elimination",
            "extension_cases": len(observed), "extension_outcomes": dict(outcomes),
            "by_base_order": {n: dict(c) for n,c in by_order.items()},
            "maximum_lc_length": max_lc, "closed_set_sizes": orbit_sizes,
            "closure_checks": closure_checks, "all_four_label_assignments": entropy_cases,
            "i3_histograms": entropy_histograms}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate", nargs="?", type=Path, default=Path(__file__).with_name("certificate.json"))
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    result = verify(json.loads(args.certificate.read_text(encoding="utf-8")))
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")

if __name__ == "__main__":
    main()
