"""Construct all unsigned quotients and pass each cyclic layout to the four-row test."""
from itertools import combinations, product
import subprocess
import sys


def quotients():
    # Two types at each fixed axis, then two neighbors of each singleton.
    axes = [(1, 0, 1)]*2 + [(0, 1, 1)]*2 + [(0, 0, 2)]*4
    single = [(0, 0)]*4 + [(1, 0)]*2 + [(0, 1)]*2

    def correction(i, j):
        a, b, c = axes[i]
        x, y = single[i]
        d, e, f = axes[j]
        z, w = single[j]
        return 5*(a*d + b*e + x*z + y*w) + c*f

    rows = []
    for i, (a, b, _) in enumerate(axes):
        x, y = single[i]
        sums = (4-2*a-x-y, 4-2*b-x-y, 4-a-b-2*y-x, 4-a-b-2*x-y)
        options = []
        for first in product(*(range(s+1) for s in sums)):
            row = tuple(v for h, s in zip(first, sums) for v in (h, s-h))
            if row[i] % 2 == 0 and sum(v*v for v in row) + row[i] == 32-correction(i, i):
                options.append(row)
        rows.append(options)

    def extend(prefix):
        i = len(prefix)
        if i == 8:
            yield prefix
            return
        for row in rows[i]:
            if all(row[j] == old[i] and row[j] + sum(x*y for x, y in zip(row, old))
                   == 20-correction(i, j) for j, old in enumerate(prefix)):
                yield from extend(prefix + [row])
    yield from extend([])


if __name__ == '__main__':
    matrices = list(quotients())
    assert len(matrices) == 16
    lines = []
    for matrix in matrices:
        entries = ' '.join(str(v) for row in matrix for v in row)
        for i, j in combinations(range(4), 2):
            lines.append(f'{(1 << i) | (1 << j)} {entries}')
    subprocess.run([sys.argv[1]], input='\n'.join(lines), text=True, check=True)
