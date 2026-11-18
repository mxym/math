"""Verify the six-triangle core catalogue using integer arithmetic (Python 3.10+)."""
import itertools
import json
from collections import Counter
from math import gcd
from pathlib import Path

HERE = Path(__file__).resolve().parent
EDGES = tuple(itertools.combinations(range(6), 2))
PAIRS = tuple(itertools.combinations_with_replacement(range(6), 2))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def psd(matrix):
    """Symmetric elimination, with positive scaling of each Schur complement."""
    while matrix:
        pivot, *column = matrix[0]
        if pivot < 0 or (pivot == 0 and any(column)):
            return False
        tail = [row[1:] for row in matrix[1:]]
        if pivot:
            tail = [[pivot * a - x * y for a, y in zip(row, column)]
                    for row, x in zip(tail, column)]
            divisor = gcd(*(a for row in tail for a in row))
            if divisor > 1:
                tail = [[a // divisor for a in row] for row in tail]
        matrix = tail
    return True


def graph(mask):
    c = [[0] * 6 for _ in range(6)]
    for k, (i, j) in enumerate(EDGES):
        c[i][j] = c[j][i] = (mask >> k) & 1
    return c


def core_neighbours(c, shifts, columns):
    """Rows of the first 18 vertices of the 99-by-99 partial adjacency matrix."""
    n = [set() for _ in range(18)]
    for i in range(18):
        n[i].update(3 * (i // 3) + (i + s) % 3 for s in (1, 2))
    edges = [(i, j) for i, j in EDGES if c[i][j]]
    assert len(shifts) == len(edges) and all(s in '012' for s in shifts)
    for (i, j), shift in zip(edges, map(int, shifts)):
        for a in range(3):
            u, v = 3 * i + a, 3 * j + (a + shift) % 3
            n[u].add(v)
            n[v].add(u)
    assert len(columns) == 27
    for k, word in enumerate(columns):
        assert len(word) == 6 and all(s in '0123' for s in word)
        for i, s in enumerate(map(int, word)):
            if s:
                for a in range(3):
                    n[3 * i + (a + s - 1) % 3].add(18 + 3 * k + a)
    return n


def check(record):
    c = graph(record['mask'])
    k = [[3 * (i == j) - 3 * c[i][j] + 1 for j in range(6)] for i in range(6)]
    if not psd(k):
        assert 'separator' not in record and 'outer' not in record
        return 'indefinite'
    m = [[6 * (i == j) + 6 - 5 * c[i][j] - dot(c[i], c[j])
          for j in range(6)] for i in range(6)]
    allowed = set()
    for v in itertools.product(range(2), repeat=6):
        z = [1 - 3 * a for a in v]
        if psd([row + [a] for row, a in zip(k, z)] + [z + [10]]):
            allowed.add(v)
    if 'separator' in record:
        y = record['separator']
        assert len(y) == 22
        assert all(dot(y, [1] + [v[i] * v[j] for i, j in PAIRS]) >= 0 for v in allowed)
        assert dot(y, [27] + [m[i][j] for i, j in PAIRS]) < 0
        return 'separated'
    columns = record['outer']
    assert all(tuple(int(a != '0') for a in word) in allowed for word in columns)
    n = core_neighbours(c, record['shifts'], columns)
    assert all(len(row) == 14 for row in n)
    for i, j in itertools.combinations(range(18), 2):
        assert len(n[i] & n[j]) == 2 - int(j in n[i])
    return 'witness'


def main():
    catalogue = json.loads((HERE / 'cores.json').read_text())
    permutations = [[1 << EDGES.index(tuple(sorted((p[i], p[j])))) for i, j in EDGES]
                    for p in itertools.permutations(range(6))]
    covered = set()
    counts, by_size = Counter(), Counter()
    for record in catalogue:
        mask = record['mask']
        edges = [k for k in range(15) if mask >> k & 1]
        orbit = {sum(p[k] for k in edges) for p in permutations}
        assert mask in orbit and covered.isdisjoint(orbit)
        covered.update(orbit)
        status = check(record)
        counts[status] += 1
        if status == 'witness':
            by_size[len(edges)] += 1
    assert covered == set(range(1 << 15))
    assert counts == {'indefinite': 118, 'separated': 12, 'witness': 26}
    print(f'{len(catalogue)} isomorphism classes cover {len(covered)} labelled graphs.')
    print(dict(counts))
    print('Witnesses by edge count (0 to 9):', [by_size[i] for i in range(10)])


if __name__ == '__main__':
    main()
