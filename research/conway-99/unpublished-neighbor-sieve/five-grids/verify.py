"""Enumerate all five-grid arrangements and replay local contradictions."""

from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
import gzip
import json

import numpy as np

from neighborhoods import check_boundary


CORNERS = (0, 2, 6, 8)
CORNER_PERMS = list(permutations(CORNERS))
FRAMES = [tuple(perm[CORNERS.index(i)] if i in CORNERS else i for i in range(9))
          for perm in CORNER_PERMS]
ROOK = np.array([[i != j and (i//3 == j//3 or i%3 == j%3)
                  for j in range(9)] for i in range(9)], dtype=np.int16)


def base_actions():
    for perm in permutations(range(3)):
        for vertical, horizontal, transpose in product(range(2), repeat=3):
            image = []
            for i, j in product(range(3), repeat=2):
                a, b = 2-i if vertical else i, 2-j if horizontal else j
                image.append(3*b+a if transpose else 3*a+b)
            yield perm, tuple(image)


def orbit_and_stabilizer(key):
    transfers = {}
    for (p, q), code in zip(combinations(range(3), 2), key):
        step = FRAMES[code]
        transfers[p, q] = step
        transfers[q, p] = tuple(step.index(i) for i in range(9))
    orbit, stabilizer = set(), []
    for perm, image in base_actions():
        moved = tuple(FRAMES.index(tuple(image.index(transfers[perm[p], perm[q]][image[i]])
                                         for i in range(9)))
                      for p, q in combinations(range(3), 2))
        orbit.add(moved)
        if moved == key:
            stabilizer.append([9*perm[p]+image[i] for p, i in product(range(3), range(9))])
    return orbit, stabilizer


def shell_matrix(key):
    shell = np.kron(np.eye(3, dtype=np.int16), ROOK)
    for (p, q), code in zip(combinations(range(3), 2), key):
        for i, j in enumerate(FRAMES[code]):
            a, b = 9*p+i, 9*q+j
            shell[a,b] = shell[b,a] = 1
    return shell


def boundary_groups(shell):
    missing = 2-shell-shell@shell+12*np.eye(27, dtype=np.int16)
    if np.any(missing < 0):
        return []
    groups = []
    for r in range(3):
        p, q = (i for i in range(3) if i != r)
        x = 9*p+np.array(CORNERS)
        y = 9*q+np.array(CORNERS)
        block = missing[np.ix_(x,y)]
        if (block.max() > 1 or np.any(block.sum(axis=0) != 2)
                            or np.any(block.sum(axis=1) != 2)):
            return []
        forced = [tuple(sorted((9*r+4, x[a], y[b]))) for a,b in zip(*np.nonzero(block))]
        groups.append([tuple(sorted(forced))])
    for p, q, r in permutations(range(3)):
        x = 9*p+np.array([1,7])
        y = 9*q+np.array([3,5])
        layers = []
        for z in 9*r+np.array(CORNERS):
            options = []
            for mask in range(16):
                matrix = np.array([mask >> i & 1 for i in range(4)]).reshape(2,2)
                if (np.array_equal(matrix.sum(axis=1), missing[x,z]) and
                        np.array_equal(matrix.sum(axis=0), missing[y,z])):
                    rows = [tuple(sorted((x[a], y[b], z))) for a,b in zip(*np.nonzero(matrix))]
                    options.append((matrix, rows))
            layers.append(options)
        choices = [tuple(sorted(row for _, rows in choice for row in rows))
                   for choice in product(*layers)
                   if np.array_equal(sum(m for m, _ in choice), missing[np.ix_(x,y)])]
        if not choices:
            return []
        groups.append(choices)
    return groups


def representatives(groups, stabilizer):
    lookup = {rows: (i,j) for i, group in enumerate(groups) for j,rows in enumerate(group)}
    actions = []
    for image in stabilizer:
        def moved(rows):
            return tuple(sorted(tuple(sorted(image[v] for v in row)) for row in rows))
        actions.append([[lookup[moved(rows)] for rows in group] for group in groups])
    seen = set()
    for choice in product(*(range(len(g)) for g in groups)):
        if choice in seen:
            continue
        for action in actions:
            target = [-1]*9
            for i, j in enumerate(choice):
                a, b = action[i][j]
                target[a] = b
            seen.add(tuple(target))
        yield choice, [row for group,j in zip(groups,choice) for row in group[j]]


def main():
    with gzip.open(Path(__file__).with_name("witnesses.json.gz"), "rt") as file:
        certificates = json.load(file)
    seen, counts = set(), []
    for key in product(range(24), repeat=3):
        if key in seen:
            continue
        orbit, stabilizer = orbit_and_stabilizer(key)
        assert key in orbit and not (seen & orbit)
        seen |= orbit
        shell = shell_matrix(key)
        groups = boundary_groups(shell)
        if not groups:
            continue
        assert int(np.trace(shell@shell@shell)) == 6*(18+5)
        certs = certificates[",".join(map(str,key))]
        tally = Counter()
        for choice, labels in representatives(groups, stabilizer):
            witness = certs.get("".join(map(str,choice)))
            tally[check_boundary(shell, labels, witness)] += 1
        assert tally['exterior'] + tally['pair'] == len(certs)
        counts.append((key, len(orbit), sum(tally.values()), tally['shell'],
                       tally['exterior'], tally['pair']))
        print(*counts[-1], flush=True)
    assert len(seen) == 24**3
    assert [v[1:] for v in counts] == [(6,12,5,6,1),(12,10,10,0,0),(12,36,36,0,0),
                                       (12,220,220,0,0),(4,16,16,0,0),(6,3,3,0,0),
                                       (1,1231,540,691,0)]
    print("All 13,824 normalized tables and all 1,528 boundary types accounted for.")


if __name__ == "__main__":
    main()
