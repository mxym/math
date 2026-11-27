"""Direct dot products and dual line equations; no solver, no dependencies."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path

DIM = 10
SIZE = 1 << DIM
EXPECTED_POINTS = 'e6f3575e9d60d73ee0791f27c29f3fac5d95c9318548a0436e83cb87d46d691e'
F = Path(__file__).with_name('partition.tsv')


def dot(x, y):
    return (x & y).bit_count() & 1


def echelon(rows):
    pivots = {}
    for row in rows:
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row
                break
            row ^= pivots[j]
    return len(pivots)


def read_lines(path):
    lines = [tuple(map(int, row.split('\t'))) for row in path.read_text(encoding='ascii').splitlines()]
    assert len(lines) == 66 and lines == sorted(lines)
    assert all(len(line) == 3 for line in lines)
    assert all(0 < a < b < c < SIZE and a ^ b == c for a, b, c in lines)
    points = [x for line in lines for x in line]
    assert len(set(points)) == 198
    return lines, set(points)


def orthogonal_system(lines):
    for a, b, _ in lines:
        for h in range(1, SIZE):
            if not (dot(a, h) or dot(b, h)):
                for p in (a, b):
                    # Unknown entry J_ij has index i+DIM*j.
                    yield sum(h << (DIM*j) for j in range(DIM) if p >> j & 1)


def enumerate_geometry(lines, points):
    qweights, bweights, through, incidence = Counter(), Counter(), Counter(), Counter()
    all_lines = [(a, b, a ^ b) for a, b in combinations(sorted(points), 2)
                 if a ^ b > b and a ^ b in points]
    for line in all_lines:
        incidence.update(line)
    assert len(all_lines) == 726 and set(incidence.values()) == {11}
    assert set(lines).issubset(all_lines)
    for x in range(SIZE):
        pairs = [(dot(x, a), dot(x, b)) for a, b, _ in lines]
        w = sum(bool(u or v) for u, v in pairs)
        bw = sum(dot(x, p) for p in points)
        qweights[w] += 1
        bweights[bw] += 1
        assert bw == 2*w
        if x:
            contained = sum(not (u or v) for u, v in pairs)
            assert SIZE//2 > len(points) - bw == 66 + 2*contained
            through[contained] += 1
    assert qweights == {0: 1, 48: 825, 56: 198}
    assert bweights == {0: 1, 96: 825, 112: 198}
    assert through == {10: 198, 18: 825}
    return qweights, bweights, through


def main():
    lines, points = read_lines(F)
    assert echelon(points) == DIM
    digest = sha256(''.join(f'{p}\n' for p in sorted(points)).encode('ascii')).hexdigest()
    assert digest == EXPECTED_POINTS
    q, b, h = enumerate_geometry(lines, points)
    rows = list(orthogonal_system(lines))
    identity = sum(1 << (DIM*i+i) for i in range(DIM))
    assert len(rows) == 33660 and all(dot(row, identity) == 0 for row in rows)
    assert echelon(rows) == 99
    malformed = lines.copy()
    a, b_, c = malformed[0]
    malformed[0] = (a, b_, c ^ 1)
    assert malformed[0][0] ^ malformed[0][1] != malformed[0][2]
    assert len(set(p for line in lines[:-1]+[lines[0]] for p in line)) == 195
    print('direct: 66 disjoint lines, 198 nonzero points, span 10, 726 available lines, degree 11')
    print('direct: quaternary', sorted(q.items()), 'binary', sorted(b.items()))
    print('direct: hyperplane full lines', sorted(h.items()))
    print('direct: orthogonal system has 33660 rows, rank 99 of 100, kernel <I>; controls PASS')


if __name__ == '__main__':
    main()
