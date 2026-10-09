#!/usr/bin/env python3
"""Discover a finite certificate for the LC claw-free component classification.

Discovery is not trusted: check_certificate.py and verify_independent.py replay
all witnesses. No floating-point arithmetic, graph database, or solver is used.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from itertools import combinations, permutations
import json
from pathlib import Path
from typing import Iterable

Graph = tuple[int, ...]

def rows(n: int, edges: Iterable[tuple[int, int]]) -> Graph:
    a = [0] * n
    for u, v in edges:
        if not 0 <= u < n or not 0 <= v < n or u == v:
            raise ValueError("invalid edge")
        a[u] |= 1 << v
        a[v] |= 1 << u
    return tuple(a)

def representatives() -> dict[int, Graph]:
    return {
        1: (0,),
        2: rows(2, [(0, 1)]),
        3: rows(3, [(0, 1), (1, 2)]),
        4: rows(4, [(0, 1), (1, 2), (2, 3)]),
        5: rows(5, [(i, (i + 1) % 5) for i in range(5)]),
        6: rows(6, [(i, (i + 1) % 5) for i in range(5)] + [(5, i) for i in range(5)]),
    }

def local_complement(g: Graph, v: int) -> Graph:
    a = list(g)
    for u in range(len(g)):
        if g[v] >> u & 1:
            a[u] ^= g[v] ^ (1 << u)
    return tuple(a)

def find_claw(g: Graph) -> tuple[int, int, int, int] | None:
    for v, neighbors in enumerate(g):
        for a, b, c in combinations([i for i in range(len(g)) if neighbors >> i & 1], 3):
            if not ((g[a] >> b & 1) or (g[a] >> c & 1) or (g[b] >> c & 1)):
                return v, a, b, c
    return None

def extend(g: Graph, mask: int) -> Graph:
    n = len(g)
    return tuple(g[i] | (((mask >> i) & 1) << n) for i in range(n)) + (mask,)

def permuted_reps(rep: Graph) -> dict[Graph, list[int]]:
    # order maps representative vertex labels to vertex labels of the endpoint.
    out: dict[Graph, list[int]] = {}
    n = len(rep)
    for order in permutations(range(n)):
        a = [0] * n
        for i in range(n):
            for j in range(n):
                if rep[i] >> j & 1:
                    a[order[i]] |= 1 << order[j]
        out.setdefault(tuple(a), list(order))
    return out

def search(start: Graph, targets: dict[Graph, list[int]]) -> dict:
    previous: dict[Graph, tuple[Graph, int] | None] = {start: None}
    queue = deque([start])
    while queue:
        g = queue.popleft()
        claw = find_claw(g)
        if claw is not None or g in targets:
            steps = []
            h = g
            while previous[h] is not None:
                h, v = previous[h]  # type: ignore[misc]
                steps.append(v)
            result = {"lc": steps[::-1]}
            if claw is not None:
                result.update(kind="claw", claw=list(claw))
            else:
                result.update(kind="representative", order=targets[g])
            return result
        for v in range(len(g)):
            h = local_complement(g, v)
            if h not in previous:
                previous[h] = g, v
                queue.append(h)
    raise RuntimeError(f"Unclassified extension: {start!r}")

def full_orbit(root: Graph) -> list[list[int]]:
    seen = {root}
    queue = deque([root])
    while queue:
        g = queue.popleft()
        if find_claw(g) is not None:
            raise RuntimeError("A proposed negative representative has a claw in its orbit")
        for v in range(len(g)):
            h = local_complement(g, v)
            if h not in seen:
                seen.add(h)
                queue.append(h)
    return [list(g) for g in sorted(seen)]

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("certificate.json"))
    args = parser.parse_args()
    reps = representatives()
    extensions = []
    for n, rep in reps.items():
        targets = permuted_reps(reps[n+1]) if n < 6 else {}
        for mask in range(1, 1 << n):
            extensions.append({"base_order": n, "attachment": mask, **search(extend(rep, mask), targets)})
    cert = {
        "format": "lc-claw-free-extensions-v1",
        "vertex_labels": "0,...,n-1; the extension vertex has label n",
        "representatives": {str(n): list(g) for n, g in reps.items()},
        "extensions": extensions,
        "closed_claw_free_orbits": {str(n): full_orbit(g) for n, g in reps.items()},
    }
    args.output.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    summary = {
        "extensions": len(extensions),
        "extension_outcomes": dict(Counter(e["kind"] for e in extensions)),
        "maximum_lc_length": max(len(e["lc"]) for e in extensions),
        "lc_length_counts": dict(sorted(Counter(len(e["lc"]) for e in extensions).items())),
        "orbit_sizes": {n: len(o) for n, o in cert["closed_claw_free_orbits"].items()},
        "by_base_order": {n: dict(Counter(e["kind"] for e in extensions if e["base_order"]==n)) for n in reps},
    }
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
