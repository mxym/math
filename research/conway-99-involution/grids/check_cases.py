"""Enumerate grid supports up to isomorphism and exhaust their unsigned completions."""
import argparse
from itertools import combinations, permutations
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_blocks import check, golay_steps
from check_star import verify


EDGES = tuple(combinations(range(7), 2))


def representatives(size):
    remaining = {sum(1 << k for k in edge_ids)
                 for edge_ids in combinations(range(21), size)}
    relabel = [[EDGES.index(tuple(sorted((p[i], p[j])))) for i, j in EDGES]
               for p in permutations(range(7))]
    while remaining:
        mask = min(remaining)
        chosen = [i for i in range(21) if (mask >> i) & 1]
        orbit = {sum(1 << mapping[i] for i in chosen) for mapping in relabel}
        assert orbit <= remaining
        remaining -= orbit
        yield mask, len(orbit)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('executable', type=Path)
    parser.add_argument('--size', type=int, choices=[4, 5], default=5)
    args = parser.parse_args()
    exe = str(args.executable.resolve())
    verify()
    t = check(5, golay_steps())
    fixture = '\n'.join(' '.join(map(str, row)) for row in t)
    subprocess.run([exe, '--golay-test'], input=fixture, text=True, check=True)
    total, cases = 0, 0
    for mask, orbit_size in representatives(args.size):
        edges = [set(e) for k, e in enumerate(EDGES) if (mask >> k) & 1]
        if len(edges) == 5 and set.intersection(*edges):
            print(mask, 'excluded by the five-star lemma', flush=True)
        else:
            subprocess.run([exe, str(mask)], check=True)
        total += orbit_size
        cases += 1
    assert (cases, total) == {4: (10, 5985), 5: (21, 20349)}[args.size]
    print(cases, 'isomorphism classes cover', total, 'labelled supports')


if __name__ == '__main__':
    main()
