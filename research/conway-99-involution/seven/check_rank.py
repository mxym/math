"""Exclude ranks seven and nine of the signed Gram matrix over F_7. Requires NumPy."""
from collections import Counter
from itertools import combinations
import numpy as np


EYE = np.eye(12, dtype=int)
TWIN = np.arange(12) ^ 1
D = EYE[TWIN]
PAIR = np.array([EYE[i] + EYE[j] for i, j in combinations(range(12), 2)])
ROOT = np.array([EYE[2*i] + EYE[2*j+s] for i, j in combinations(range(6), 2)
                 for s in range(2)])
ROOT -= ROOT[:, TWIN]
LEGENDRE = (0, 1, 1, -1, 1, -1, -1)


def matchings(points):
    if not points:
        yield ()
        return
    a = points[0]
    for b in points[1:]:
        for tail in matchings(tuple(x for x in points[1:] if x != b)):
            yield ((a, b),) + tail


def partitions(total, least=1):
    if not total:
        yield ()
    for first in range(least, total + 1):
        for tail in partitions(total-first, first):
            yield (first,) + tail


def axis_types():
    all_matchings = []
    for edges in matchings(tuple(range(12))):
        perm = list(range(12))
        for a, b in edges:
            perm[a], perm[b] = b, a
        all_matchings.append(tuple(perm))
    assert len(all_matchings) == 10395
    for part in partitions(6):
        direct = list(range(12))
        generators = []
        start = previous = 0
        for half in part:
            size = 2*half
            def cycle_map(f):
                g = list(range(12))
                g[start:start+size] = [start + f(i) % size for i in range(size)]
                return g
            generators.append(cycle_map(lambda i: 1-i))
            if half > 1:
                generators.append(cycle_map(lambda i: i+2))
            if half == previous:
                g = list(range(12))
                g[start-size:start], g[start:start+size] = g[start:start+size], g[start-size:start]
                generators.append(g)
            for i in range(0, size, 2):
                a, b = start+i+1, start+(i+2)%size
                direct[a], direct[b] = b, a
            start += size
            previous = half
        inverses = [np.argsort(g).tolist() for g in generators]
        seen = set()
        for opposite in all_matchings:
            if opposite in seen:
                continue
            seen.add(opposite)
            pending = [opposite]
            while pending:
                cur = pending.pop()
                for g, inverse in zip(generators, inverses):
                    other = tuple(g[cur[i]] for i in inverse)
                    if other not in seen:
                        seen.add(other)
                        pending.append(other)
            yield np.array(direct), np.array(opposite)
        assert len(seen) == 10395


def eliminate(matrix):
    """Return a row-operation matrix, pivot column indices and the determinant if square."""
    a = matrix.copy() % 7
    transform = np.eye(len(a), dtype=int)
    pivots = []
    determinant = 1
    for j in range(a.shape[1]):
        r = len(pivots)
        available = np.flatnonzero(a[r:, j])
        if not len(available):
            continue
        k = r + int(available[0])
        if r != k:
            a[[r,k]] = a[[k,r]]
            transform[[r,k]] = transform[[k,r]]
            determinant = -determinant
        pivot = int(a[r,j])
        determinant = determinant*pivot % 7
        inv = pow(pivot, -1, 7)
        a[r] = a[r]*inv % 7
        transform[r] = transform[r]*inv % 7
        scale = a[:,j].copy()
        scale[r] = 0
        a = (a - scale[:,None]*a[r]) % 7
        transform = (transform - scale[:,None]*transform[r]) % 7
        pivots.append(j)
    return transform, pivots, determinant if len(pivots) == len(a) else 0


def exterior_domains(direct, opposite, transform, pivots, inverse):
    first, second = np.where(~np.eye(len(PAIR), dtype=bool))
    fixed_double = direct == opposite
    allowed = np.all(PAIR[first][:,fixed_double]*PAIR[second][:,fixed_double] == 0, axis=1)
    signed = PAIR[first[allowed]] - PAIR[second[allowed]]
    signed = np.unique(signed, axis=0)
    result = []
    for root in ROOT:
        col = -4*signed-root
        v = col[:,pivots] % 7
        residual_norm = (10-np.sum((v @ inverse % 7)*v, axis=1)) % 7
        radical = col @ transform[len(pivots):].T % 7
        result.append((v, radical, residual_norm))
    return result


def pass_pair_test(domains, inverse, coefficient):
    metric = np.zeros((len(inverse)+1, len(inverse)+1), dtype=int)
    metric[:-1,:-1] = inverse
    metric[-1,-1] = coefficient
    points = []
    for coords, radical, norm in domains:
        zero = np.all(radical == 0, axis=1)
        parts = []
        for t in range(7 if coefficient else 1):
            v = coords[zero & (norm == coefficient*t*t % 7)]
            parts.append(np.column_stack((v, np.full(len(v), t))))
        points.append(np.unique(np.vstack(parts), axis=0))
    if any(len(v) == 0 for v in points):
        return False, False

    products = {}
    active = [np.ones(len(v), dtype=bool) for v in points]
    for i, j in combinations(range(30), 2):
        shift = ROOT[i,::2] @ ROOT[j,::2]
        ok = np.isin((points[i] @ metric @ points[j].T + shift) % 7, [0, 3, 4])
        products[i,j], products[j,i] = ok, ok.T
    while True:
        before = sum(int(a.sum()) for a in active)
        for i in range(30):
            for j in range(30):
                if j != i:
                    active[i] &= products[i,j][:,active[j]].any(axis=1)
            if not active[i].any():
                return True, False
        if sum(int(a.sum()) for a in active) == before:
            return True, True


def check_rank(rank, direct, opposite, gram, transform, pivots):
    s = len(pivots)
    inverse, _, delta = eliminate(gram[np.ix_(pivots,pivots)])
    assert delta and np.array_equal(inverse @ gram[np.ix_(pivots,pivots)] % 7,
                                    np.eye(s, dtype=int))
    gap = rank-s
    character = -(-1)**((15-rank)//2)
    if gap == 0 and LEGENDRE[delta] != character:
        return False, False
    domains = exterior_domains(direct, opposite, transform, pivots, inverse)
    if gap <= 1:
        coeff = 0 if gap == 0 else (1 if LEGENDRE[delta] == character else 3)
        return pass_pair_test(domains, inverse, coeff)
    assert gap == 2
    # The anchor radical maps to a totally isotropic subspace in the residual plane.
    split = LEGENDRE[-delta % 7]*character == 1
    common_lines = None
    for _, radical, _ in domains:
        if np.all(radical == 0, axis=1).any():
            continue
        if not split:
            return False, False
        first = np.argmax(radical != 0, axis=1)
        units = np.array([0,1,4,5,2,3,6])[radical[np.arange(len(radical)),first]]
        lines = set(map(tuple, radical*units[:,None] % 7))
        common_lines = lines if common_lines is None else common_lines & lines
        if not common_lines:
            return False, False
    return True, True


def main():
    histogram = Counter()
    singles, pairs = Counter(), Counter()
    for direct, opposite in axis_types():
        gram = 11*EYE + D - 4*EYE[direct] + 4*EYE[opposite] - 1
        transform, pivots, _ = eliminate(gram)
        s = len(pivots)
        histogram[s] += 1
        for r in (7, 9):
            if s <= r:
                one, two = check_rank(r, direct, opposite, gram, transform, pivots)
                singles[r] += int(one)
                pairs[r] += int(two)
    print("axis ranks", sorted(histogram.items()))
    print("one-column survivors", dict(singles), "pair-compatible survivors", dict(pairs))
    assert histogram == {7:3, 8:5, 9:97, 10:637, 11:2838}
    assert singles == {7:0, 9:12} and pairs == {7:0, 9:0}


if __name__ == '__main__':
    main()
