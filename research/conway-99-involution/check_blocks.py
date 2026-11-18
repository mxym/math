"""Check the two orbit identities and recover every edge of two known SRGs."""
from itertools import combinations, product


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def check(dimension, steps):
    points = list(product(range(3), repeat=dimension))
    zero = (0,) * dimension
    neg = lambda v: tuple(-x % 3 for x in v)
    assert steps == {neg(v) for v in steps} and zero not in steps
    neighbours = {v: {tuple((a + b) % 3 for a, b in zip(v, w)) for w in steps}
                  for v in points}
    for v, w in combinations(points, 2):
        assert len(neighbours[v] & neighbours[w]) == 2 - int(v in neighbours[w])
    axes = sorted(v for v in steps if v < neg(v))
    reps = []
    x, z = [[] for _ in axes], [[] for _ in axes]
    for v in points:
        if v in steps or not v < neg(v):
            continue
        support = [i for i, a in enumerate(axes) if {a, neg(a)} & neighbours[v]]
        assert len(support) == 2
        if axes[support[0]] not in neighbours[v]:
            v = neg(v)
        reps.append(v)
        for i, a in enumerate(axes):
            pos, other = int(a in neighbours[v]), int(neg(a) in neighbours[v])
            x[i].append(pos + other)
            z[i].append(pos - other)
    t, l = [], []
    for v in reps:
        direct = [int(w in neighbours[v]) for w in reps]
        flipped = [int(neg(w) in neighbours[v]) for w in reps]
        t.append([a + b for a, b in zip(direct, flipped)])
        l.append([a - b for a, b in zip(direct, flipped)])
    k = len(steps)
    xt, zt = list(zip(*x)), list(zip(*z))
    for i, v in enumerate(reps):
        assert sum(t[i]) == k - 2 and t[i].count(2) == 1 and t[i][i] == 0
        assert all(dot(row, t[i]) == 4 - 2 * row[i] for row in x)
        assert all(dot(row, l[i]) == 0 for row in z)
        for j, w in enumerate(reps):
            assert dot(t[i], t[j]) + t[i][j] == (k - 2) * (i == j) + 4 - dot(xt[i], xt[j])
            assert dot(l[i], l[j]) + l[i][j] == (k - 2) * (i == j) - dot(zt[i], zt[j])
            for u, s in ((v, 1), (neg(v), -1)):
                for y, h in ((w, 1), (neg(w), -1)):
                    assert t[i][j] + s*h*l[i][j] == 2 * int(y in neighbours[u])
    print(f'{len(points)} vertices, {len(axes)} axes, {len(reps)} exterior pairs: all checks passed.')
    def label(i):
        a, b = (j for j, value in enumerate(xt[i]) if value)
        return a, b, z[b][i] < 0
    order = sorted(range(len(reps)), key=label)
    return [[t[i][j] for j in order] for i in order]


def golay_steps():
    steps, v = set(), (1, 0, 0, 0, 0)
    for _ in range(11):
        steps.update((v, tuple(-x % 3 for x in v)))
        a, b, c, d, e = v
        v = e, (a + e) % 3, (b - e) % 3, (c + e) % 3, d
    return steps


if __name__ == '__main__':
    check(2, {(1, 0), (2, 0), (0, 1), (0, 2)})
    check(5, golay_steps())
