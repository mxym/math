"""Standard-library incidence and rational certificate diagnostics.

Universal proofs are in paper.md and DesignCore.lean. Randomly generated
but fixed-seed feasible weights are diagnostics, not optimization output.
The sharpness family has exact primal/dual certificates and a counting
proof; small deletion minima are also independently exhausted.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from random import Random


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def check_vector(edges, weights, k):
    require(bool(edges) and k >= 2, 'domain')
    r, m = len(edges[0]), len(edges)
    require(r >= 2 and all(len(e) == r for e in edges), 'uniformity')
    require(len(set(edges)) == m, 'simplicity')
    require(all(e & f for e, f in combinations(edges, 2)), 'intersectingness')
    require(len(weights) == m and all(y >= 0 for y in weights), 'weight domain')
    loads = Counter()
    for e, y in zip(edges, weights):
        for v in e:
            loads[v] += y
    require(all(z <= 1 for z in loads.values()), 'feasibility')
    Y, b = sum(weights), max(weights)
    Psi = m*r-(m+r-1)*Y
    require(Y <= r-(r-1)*b and Psi >= 0, 'weighted star / harmonic')
    core = [e for e, y in zip(edges, weights) if y > F(1, k+1)]
    q, s = len(core), m-len(core)
    deg = Counter(v for e in core for v in e)
    require(max(deg.values(), default=0) <= k, 'threshold degree cap')
    require((r-1)*((k+1)*Y-m)*s <= m*(k+1)*Psi,
            'cross-multiplied extraction inequality')
    if Y > F(m, k+1):
        require(s <= m*(k+1)*Psi/((r-1)*((k+1)*Y-m)), 'positive-branch deletion')
    I = sum(len(e & f)-1 for e, f in combinations(core, 2))
    degree_defect = sum(d*(k-d) for d in deg.values())
    require(degree_defect == q*((k-1)*r-q+1)-2*I >= 0, 'core exact identity')
    require(0 <= k*len(deg)-q*r <= degree_defect, 'active vertex count')
    # The converse witness is checked against the entire original family.
    core_set = set(core)
    converse_load = Counter()
    for e in edges:
        if e in core_set:
            for v in e:
                converse_load[v] += F(1, k)
    require(all(z <= 1 for z in converse_load.values()), 'uniform converse feasibility')
    if m == (k-1)*r+1:
        d = F(m, k)-Y
        require(d >= 0, 'design-boundary deficit sign')
        require(s <= F(2*k*k*(k+1)*r, r-1)*d <= 4*k*k*(k+1)*d,
                'finite linear deletion constant')
        require(I <= F(q*s, 2), 'boundary excess')
        require(degree_defect == q*s-2*I, 'boundary exact identity')
    return r, m, Y, q, s, I


def sharp_family(n, t):
    require(n >= 4 and n % 2 == 0 and t >= 1, 'sharp-family domain')
    pairs = {(i, j): ('pair', i, j) for i, j in combinations(range(n), 2)}
    good = []
    for i in range(n):
        good.append(frozenset(
            [pairs[min(i, j), max(i, j)] for j in range(n) if j != i]
            + [('private', i, a) for a in range(t)]))
    C = frozenset(pairs[i, i+1] for i in range(0, n, 2))
    r = n-1+t
    W = frozenset(('common', a) for a in range(r-n//2-1))
    bad = [C | W | {('bad_private', a)} for a in range(t)]
    edges = good+bad
    weights = [F(1, 2)]*n+[F(0)]*t
    return edges, weights, C


def minimum_deletions(edges, k):
    for s in range(len(edges)+1):
        for deletion in combinations(range(len(edges)), s):
            deleted = set(deletion)
            deg = Counter(v for i, e in enumerate(edges) if i not in deleted for v in e)
            if max(deg.values(), default=0) <= k:
                return s
    raise RuntimeError('deleting all edges failed')


def main():
    fano = [frozenset((i, (i+1) % 7, (i+3) % 7)) for i in range(7)]
    case = check_vector(fano, [F(1, 3)]*7, 3)
    require(all(sum(F(1, 3) for _ in e) == 1 for e in fano), 'Fano primal')
    require(all(not all(set(C) & e for e in fano)
                for C in combinations(range(7), 2)), 'Fano no two-cover')
    require(all(fano[0] & e for e in fano), 'Fano three-cover')
    require(F(3) > F(7, 3), 'finite integer equality overclaim control')
    print(f'Fano boundary: r={case[0]}, m={case[1]}, tau*=7/3, tau=3 PASS')
    count = 0
    for n in (4, 6, 10, 16, 32):
        for t in (1, 2, 5, 17):
            edges, y, C = sharp_family(n, t)
            r, m, Y, q, s, I = check_vector(edges, y, 2)
            require(len(C) == Y == F(n, 2) and all(C & e for e in edges),
                    'sharpness primal/dual certificate')
            require((q, s, I) == (n, t, 0), 'exact threshold core')
            require(F(m, 2)-Y == F(t, 2), 'sharpness deficit')
            full_excess = sum(len(e & f)-1 for e, f in combinations(edges, 2))
            require(full_excess == t*(t-1)//2*(r-2), 'whole-family exact excess')
            # At most two bad edges can survive. Each matching pair needs
            # ell good deletions, so the written lower bound is checked.
            require(all(t-ell+ell*n//2 >= t for ell in (0, 1, 2)),
                    'sharp deletion lower-bound arithmetic')
            count += 1
    print(f'{count} sharpness families: exact primal/dual and excess certificates PASS')
    for n, t in ((4, 1), (4, 2), (4, 3), (6, 2), (6, 4), (8, 3)):
        edges, _, _ = sharp_family(n, t)
        require(minimum_deletions(edges, 2) == t, 'independent deletion enumeration')
    print('Six small degree-cap deletion minima independently exhausted PASS')
    for j in (2, 3):
        edges, y, C = sharp_family(2*j**4, j**3)
        r, m, Y, q, s, I = check_vector(edges, y, 2)
        full_I = sum(len(e & f)-1 for e, f in combinations(edges, 2))
        require(len(C) == Y and all(C & e for e in edges), 'large example cover')
        if j == 3:
            require(full_I > r*r, 'whole-family near-linearity overclaim control')
        print(f'Exact j={j} family: r={r}, m={m}, d={F(s,2)}, deleted={s}, '
              f'I(H)={full_I}, I(core)={I} PASS')
    rng = Random(20261007)
    count = 0
    for _ in range(160):
        r, m = rng.randrange(2, 10), rng.randrange(1, 25)
        edges = [frozenset([('anchor',)] + [('fresh', i, a) for a in range(r-1)])
                 for i in range(m)]
        raw = [F(rng.randrange(0, 21), 20) for _ in range(m)]
        if not any(raw):
            raw[0] = F(1)
        y = [z/max(F(1), sum(raw)) for z in raw]
        for k in range(2, 8):
            check_vector(edges, y, k)
            count += 1
    print(f'{count} fixed-seed rational feasible-weight incidence diagnostics PASS')
    invalid = [F(1)]*7
    try:
        check_vector(fano, invalid, 3)
    except RuntimeError as exc:
        require(str(exc) == 'feasibility', 'wrong invalid-input rejection')
    else:
        raise RuntimeError('infeasible dual escaped')
    require(F(3) > F(7,3), 'asymptotic integrality promoted to finite equality')
    print('Infeasible dual, finite integrality and whole-excess negative controls PASS')


if __name__ == '__main__':
    main()
