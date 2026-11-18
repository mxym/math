"""Enumerate the 3K2 quotient branch. Pass the compiled matching_rows executable."""
import argparse
import itertools
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

from check_cores import dot

U_EDGES = tuple(itertools.combinations(range(6), 2))
PAIRS = tuple(itertools.combinations_with_replacement(range(7), 2))


def six_orbits():
    degree = [4, 4, 2, 2, 2, 2]
    double_capacity = [1, 1, 2, 2, 2, 2]
    permutations = [p + q for p in itertools.permutations(range(2))
                    for q in itertools.permutations(range(2, 6))]
    orders = [[U_EDGES.index(tuple(sorted((p[i], p[j])))) for i, j in U_EDGES]
              for p in permutations]
    weights = []

    def extend(k):
        if k == len(U_EDGES):
            if not any(degree) and all(weights <= [weights[a] for a in order] for order in orders):
                yield tuple(weights)
            return
        i, j = U_EDGES[k]
        for value in range(min(degree[i], degree[j], 2) + 1):
            if value == 2 and min(double_capacity[i], double_capacity[j]) == 0:
                continue
            if j == 5 and degree[i] != value:
                continue
            weights.append(value)
            for v in (i, j):
                degree[v] -= value
                double_capacity[v] -= value == 2
            yield from extend(k + 1)
            for v in (i, j):
                degree[v] += value
                double_capacity[v] += value == 2
            weights.pop()

    yield from extend(0)


def small_block(edges):
    block = [[0] * 7 for _ in range(7)]
    for j in (1, 2):
        block[0][j] = block[j][0] = 2
    for (i, j), weight in zip(U_EDGES, edges):
        block[i + 1][j + 1] = block[j + 1][i + 1] = weight
    return block


def mixed_target(block, w):
    return tuple(6 - w[i] - dot(row, w) - 3 * (i == 0) for i, row in enumerate(block))


def profiles(block, moments):
    for b in (0, 1):
        for u in itertools.product(range(3), repeat=6):
            w = (b,) + u
            if sum(u) != 3 + b or min(mixed_target(block, w)) < 0:
                continue
            if all(w[i] * w[j] <= moments[i][j] for i, j in PAIRS):
                yield w


def column_multisets(allowed, degrees, moments):
    """Extend seven rows within cells of equal column prefixes, modulo column permutations."""
    prefix = [{w[:r] for w in allowed} for r in range(8)]

    def extend(r, cells):
        if r == 7:
            yield tuple(p for p, size in cells for _ in range(size))
            return
        twos = (moments[r][r] - degrees[r]) // 2
        ones = degrees[r] - 2 * twos
        assert 2 * twos + degrees[r] == moments[r][r]
        target = tuple(moments[r][:r])

        def fill(k, one, two, needed, parts):
            if k == len(cells):
                if one == two == 0 and not any(needed):
                    yield from extend(r + 1, parts)
                return
            p, size = cells[k]
            for b in range(min(size, two) + 1):
                for a in range(min(size - b, one) + 1):
                    counts = (size - a - b, a, b)
                    new = [(p + (v,), n) for v, n in enumerate(counts) if n]
                    if any(q not in prefix[r + 1] for q, _ in new):
                        continue
                    rest = tuple(n - (a + 2 * b) * t for n, t in zip(needed, p))
                    if all(n >= 0 for n in rest):
                        yield from fill(k + 1, one - a, two - b, rest, parts + new)

        yield from fill(0, ones, twos, target, [])

    yield from extend(0, [((), 20)])


# Each form is nonnegative on all allowed columns in the case where it is used.
FORMS = (
    [(0, 1, -3), (0, 2, -3)] + [(0, j, 1) for j in range(3, 7)],
    [(0, 2, -1), (2, 2, -2)] + [(2, j, 1) for j in range(3, 7)],
    [(1, 2, -1)],
)


def main(executable):
    stats = Counter()
    cases = list(six_orbits())
    assert len(cases) == 9
    for case, edges in enumerate(cases):
        block = small_block(edges)
        degrees = [14 - sum(row) - 6 * (i == 0) for i, row in enumerate(block)]
        m = [[12 * (i == j) + 6 - block[i][j] - dot(block[i], block[j])
              - 6 * (i == j == 0) for j in range(7)] for i in range(7)]
        if min(map(min, m)) < 0:
            stats['negative moment'] += 1
            continue
        allowed = list(profiles(block, m))
        if any(sum(c * m[i][j] for i, j, c in form) < 0
               and all(sum(c * w[i] * w[j] for i, j, c in form) >= 0 for w in allowed)
               for form in FORMS):
            stats['separating form'] += 1
            continue

        count = 0
        with subprocess.Popen([executable], stdin=subprocess.PIPE, text=True) as solver:
            for columns in column_multisets(allowed, degrees, m):
                for w in columns:
                    print(*w, *mixed_target(block, w), file=solver.stdin)
                count += 1
            solver.stdin.close()
            if solver.wait() != 0:
                raise RuntimeError(f'residual search failed in case {case}')
        print(f'U case {case} checked {count} incidence multisets.', flush=True)
        stats['multisets'] += count
    assert stats == {'negative moment': 4, 'separating form': 3, 'multisets': 2754}
    print(dict(stats))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('executable', type=Path)
    main(parser.parse_args().executable.resolve())
