"""Test transitive actions on triangle contacts with GAP's degree-twelve list."""
from collections import Counter
from functools import cache
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import re
import sys


IDENTITY = tuple(range(12))
PAIRS = tuple(combinations(IDENTITY, 2))
EXPECTED_SHA256 = "8661c218ff24ffe448ab4967d32bdb43a8d256b33ee86217e64cca7736ad17fa"


def groups(path):
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED_SHA256
    table = raw.decode().split("TRANSGRP[12]:=")[1].split("];")[0].strip()[1:]
    record = re.compile(r'\[\s*((?:(?:\s*\([\d,\s]+\))+\s*,\s*)+)"[^"]*"\s*\]')
    records = list(record.finditer(table))
    assert len(records) == 301 and set(record.sub("", table)) <= set(", \r\n\t")
    for record in records:
        generators = []
        fields = "".join(record.group(1).split())[:-1]
        for field in re.split(r"(?<=\)),(?=\()", fields):
            assert re.fullmatch(r"(?:\([\d,]+\))+", field)
            permutation = list(IDENTITY)
            moved = set()
            for cycle in re.findall(r"\(([\d,]+)\)", field):
                points = [int(x)-1 for x in cycle.split(",")]
                assert not moved.intersection(points)
                moved.update(points)
                for i,j in zip(points,points[1:]+points[:1]):
                    permutation[i] = j
            assert sorted(permutation) == list(IDENTITY)
            generators.append(tuple(permutation))
        yield generators


def equivariant_map(generators, source, target):
    """Propagate one basepoint image along generator-labeled orbit edges."""
    images = {source: target}
    pending = [source]
    while pending:
        i = pending.pop()
        for generator in generators:
            a, b = generator[i], generator[images[i]]
            if a not in images:
                images[a] = b
                pending.append(a)
            elif images[a] != b:
                return None
    return images if len(set(images.values())) == len(images) else None


def check_group(generators):
    centralizer = []
    for point in IDENTITY:
        image = equivariant_map(generators,0,point)
        if image is not None:
            centralizer.append(tuple(image[i] for i in IDENTITY))
    mates = [p for p in centralizer if p[0] and all(p[p[i]] == i for i in IDENTITY)]
    if not mates:
        return 0, 0, 0
    assert all(all(p[i] != i for i in IDENTITY) for p in mates)
    actions = [tuple(PAIRS.index(tuple(sorted((g[i],g[j])))) for i,j in PAIRS)
               for g in generators]
    remaining = set(range(66))
    orbits = []
    while remaining:
        root = min(remaining)
        orbit = sorted(equivariant_map(actions,root,root))
        orbits.append(orbit)
        remaining.difference_update(orbit)

    @cache
    def orbit_images(source, target):
        left, right = orbits[source], orbits[target]
        if len(left) != len(right):
            return []
        answer = []
        for target_pair in right:
            mapping = equivariant_map(actions,left[0],target_pair)
            if mapping is not None:
                count = Counter(j for i in left if 0 in PAIRS[i] for j in PAIRS[mapping[i]])
                answer.append((tuple(count.items()),tuple(mapping[i] for i in left)))
        return answer

    @cache
    def nonmate_orbits(mate):
        result = []
        for i, orbit in enumerate(orbits):
            a,b = PAIRS[orbit[0]]
            if mate[a] != b:
                result.append(i)
        assert sum(len(orbits[i]) for i in result) == 60
        return result

    @cache
    def two_wing_maps(mate_a, mate_b, direct, indirect):
        capacity = [2]*12
        for j in (direct[0], direct[mate_a[0]], mate_b[direct[0]], indirect[0]):
            capacity[j] -= 1
        if min(capacity) < 0:
            return []
        source = nonmate_orbits(mate_a)
        options = [[(j,hist,mapping) for j in nonmate_orbits(mate_b)
                    for hist,mapping in orbit_images(i,j)
                    if all(capacity[k] >= n for k,n in hist)] for i in source]
        order = sorted(range(len(source)),key=lambda i:len(options[i]))
        selected = [None]*len(source)
        found = []

        def visit(depth, used):
            if depth == len(source):
                assert not any(capacity)
                mapping = bytearray(range(66))
                for orbit, images in zip(source,selected):
                    for i,j in zip(orbits[orbit],images):
                        mapping[i] = j
                found.append(bytes(mapping))
                return
            i = order[depth]
            for j,hist,mapping in options[i]:
                if j in used or any(capacity[k] < n for k,n in hist):
                    continue
                for k,n in hist:
                    capacity[k] -= n
                selected[i] = mapping
                visit(depth+1, used | {j})
                for k,n in hist:
                    capacity[k] += n

        visit(0, set())
        return found

    tested = pairwise_feasible = compatible = 0
    for a,b,c,ac in product(mates,mates,mates,centralizer):
        tested += 1
        ab = two_wing_maps(a,b,IDENTITY,ac)
        bc = two_wing_maps(b,c,IDENTITY,ac)
        direct = two_wing_maps(a,c,ac,IDENTITY)
        if not (ab and bc and direct):
            continue
        pairwise_feasible += 1
        first_pairs = bytes(i for orbit in nonmate_orbits(a) for i in orbits[orbit])
        targets = {bytes(mapping[i] for i in first_pairs) for mapping in direct}
        sources = [bytes(mapping[i] for i in first_pairs) for mapping in ab]
        for mapping in bc:
            translation = mapping + bytes(256-len(mapping))
            compatible += sum(u.translate(translation) in targets for u in sources)
    return tested, pairwise_feasible, compatible


if __name__ == "__main__":
    stats = [check_group(row) for row in groups(Path(sys.argv[1]))]
    counts = tuple(sum(column) for column in zip(*stats))
    assert sum(s[0] > 0 for s in stats) == 182
    assert counts == (7574,135,0)
    print("301 groups, 182 with a mate:", counts)
