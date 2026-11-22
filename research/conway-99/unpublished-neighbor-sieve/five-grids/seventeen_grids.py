"""Check all projected triangle counts when precisely four cells fail."""

from collections import Counter
from itertools import combinations_with_replacement, permutations, product

from complete_point_exclusion import CELLS, LOCAL, TRIANGLES


LEFT = CELLS.index((0,1))
RIGHT = CELLS.index((2,3))
INACTIVE = (4,5,6)
DIRTY = [CELLS.index((a,b)) for a in (0,1) for b in (2,3)]
CORES = {k:CELLS.index(tuple(v for v in INACTIVE if v != k)) for k in INACTIVE}
REGULAR = [a for a in range(21) if a not in DIRTY and a not in CORES.values()]


def mixed(axis, k):
    return CELLS.index((axis,k))


def add(counts, *cells):
    counts[tuple(sorted(cells))] += 2


def prescribed_triangles(caps):
    from_dirty = Counter()
    from_core = Counter()
    for d, cap in caps.items():
        i,j = CELLS[d]
        u,v = 1-i,5-j
        for a,b in permutations([k for k in INACTIVE if k != cap]):
            add(from_dirty, d, mixed(u,a), CORES[a])
            add(from_dirty, d, mixed(v,b), CORES[b])
            add(from_dirty, d, mixed(u,b), mixed(v,cap))
            add(from_dirty, d, mixed(u,cap), mixed(v,a))
    for k, core in CORES.items():
        for pair in [(DIRTY[0],DIRTY[3]), (DIRTY[1],DIRTY[2])]:
            unpaired = [d for d in pair if caps[d] != k]
            for d in unpaired:
                i,j = CELLS[d]
                add(from_core, core, d, mixed(1-i,k))
                add(from_core, core, d, mixed(5-j,k))
            if len(unpaired) == 2:
                add(from_core, core, LEFT, RIGHT)
            else:
                d, = unpaired
                i,j = CELLS[d]
                add(from_core, core, LEFT, mixed(j,k))
                add(from_core, core, RIGHT, mixed(i,k))
    for t in TRIANGLES:
        if any(i in DIRTY for i in t) and any(i in CORES.values() for i in t):
            assert from_dirty[t] == from_core[t]
    from_core.update({t:n for t,n in from_dirty.items() if all(i not in CORES.values() for i in t)})
    return from_core


def candidates():
    charts = {}
    for a in REGULAR:
        triangles = [t for t in TRIANGLES if a in t]
        rows = []
        for choices in combinations_with_replacement(LOCAL[a],4):
            rows.append({t:sum(tuple(b for b in t if b != a) in m for m in choices)
                         for t in triangles})
        assert len(rows) == 126
        charts[a] = rows
    return charts


def main():
    charts = candidates()
    failures = Counter()
    for positions in product(INACTIVE, repeat=4):
        if positions[0] == positions[3] or positions[1] == positions[2]:
            continue
        required = prescribed_triangles(dict(zip(DIRTY,positions)))
        chosen = {}
        for a in REGULAR:
            rows = [row for row in charts[a] if all(n == required[t] for t,n in row.items()
                                                    if any(b not in REGULAR for b in t))]
            assert len(rows) == 1
            chosen[a], = rows
        inconsistent = sum(len({chosen[a][t] for a in t}) > 1 for t in TRIANGLES
                           if all(a in REGULAR for a in t))
        failures[inconsistent] += 1
    assert sum(failures.values()) == 36 and min(failures) > 0
    print("Inconsistent triangle counts per cap assignment:", dict(sorted(failures.items())))


if __name__ == "__main__":
    main()
