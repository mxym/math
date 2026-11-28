#!/usr/bin/env python3
"""Complete ordinal proof for the four mixed A4-equivariant EFX cases."""
from collections import Counter
from itertools import permutations, product

if not __debug__:
    raise RuntimeError("run without Python -O")

PLAYERS = tuple(range(4))
GROUP = tuple(p for p in permutations(PLAYERS)
              if sum(p[i] > p[j] for i in PLAYERS for j in range(i+1, 4)) % 2 == 0)
EDGES = tuple((i, j) for i in PLAYERS for j in range(i+1, 4))
MATCHINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
LIMIT = 1 << 8

def action(shape):
    def extend(p, d):
        if d == 1:
            return (0,)
        if d == 4:
            return p
        if d == 6:
            return tuple(EDGES.index(tuple(sorted(p[i] for i in e))) for e in EDGES)
        if d == 3:
            return tuple(MATCHINGS.index(tuple(sorted(tuple(sorted(p[i] for i in e))
                                                      for e in f))) for f in MATCHINGS)
        raise ValueError(d)
    out = {}
    for p in GROUP:
        pp = []
        shift = 0
        for d in shape:
            pp.extend(shift + j for j in extend(p, d))
            shift += d
        out[p] = tuple(pp)
        assert sorted(pp) == list(range(8))
    for p in GROUP:
        for q in GROUP:
            pq = tuple(p[q[i]] for i in PLAYERS)
            assert tuple(out[p][out[q][x]] for x in range(8)) == out[pq]
    return out

def mask_action(p):
    masks = [0] * LIMIT
    for x in range(1, LIMIT):
        b = x & -x
        masks[x] = masks[x ^ b] | (1 << p[b.bit_length()-1])
    return masks

def all_allocations():
    for a in product(PLAYERS, repeat=8):
        bundles = [0] * 4
        for g, i in enumerate(a):
            bundles[i] |= 1 << g
        if all(bundles):
            yield tuple(bundles)

def arcs_for(shape, top, allocations):
    # A single preference table at player 0, modulo its stabilizer.
    # Two compared symbols coincide exactly when they are in the same orbit
    # of (player, bundle). Transport each player to 0 in every possible way.
    pp = {p: mask_action(z) for p, z in action(shape).items()}
    rep = [[min(pp[p][S] for p in GROUP if p[i] == 0) for S in range(LIMIT)]
           for i in PLAYERS]
    names = sorted({rep[0][S] for S in range(LIMIT) if S.bit_count() <= 5})
    index = {s: j for j, s in enumerate(names)}
    v = [[index.get(s) for s in row] for row in rep]

    # R is reflexive reachability, so R[x][y] is forced x<=y and represents
    # strict inequality if x!=y. Larger bundles never occur in comparisons.
    R = [1 << j for j in range(len(names))]
    for S in range(LIMIT):
        if S.bit_count() >= 5:
            continue
        x = v[0][S]
        for g in range(8):
            if not ((S >> g) & 1):
                y = v[0][S | (1 << g)]
                assert x != y
                R[x] |= 1 << y
    t = v[0][1 << top]
    for g in range(8):
        x = v[0][1 << g]
        if x != t:
            R[x] |= 1 << t
    for k in range(len(R)):
        for j in range(len(R)):
            if (R[j] >> k) & 1:
                R[j] |= R[k]
    assert all(not ((R[y] >> x) & 1 and (R[x] >> y) & 1)
               for x in range(len(R)) for y in range(x))

    trim = [[S ^ (1 << g) for g in range(8) if (S >> g) & 1 and S != (1 << g)]
            for S in range(LIMIT)]
    C = set()
    for A in allocations:
        # The clause is a disjunction of strict-envy witnesses for A.
        D = {(v[i][A[i]], v[i][B]) for i in PLAYERS for j in PLAYERS
             if i != j for B in trim[A[j]]}
        if any(x != y and (R[x] >> y) & 1 for x, y in D):
            continue
        D = {(x, y) for x, y in D if not ((R[y] >> x) & 1)}
        # If x<y already implies another literal z<t in this clause,
        # then x<y is dispensable, by z<=x<y<=t.
        D = tuple(sorted((x, y) for x, y in D if not any(
            (z, t) != (x, y) and (R[z] >> x) & 1 and (R[y] >> t) & 1
            for z, t in D)))
        C.add(D)
    # Clause subsumption, logically redundant but reduces reproduction time.
    F = []
    seen = []
    for c in sorted(C, key=lambda c: (len(c), c)):
        s = set(c)
        if not any(old <= s for old in seen):
            F.append(c)
            seen.append(s)
    return R, F

def add_arc(R, x, y):
    if (R[y] >> x) & 1:
        return None
    if (R[x] >> y) & 1:
        return R
    # Only paths through the new edge need to be added.
    return [row | R[y] if (row >> x) & 1 else row for row in R]

def refute(R, F):
    nodes = 0
    def visit(R, F):
        nonlocal nodes
        nodes += 1
        live, units = [], []
        for c in F:
            if any((R[x] >> y) & 1 for x, y in c):
                continue
            d = [(x, y) for x, y in c if not ((R[y] >> x) & 1)]
            if not d:
                return True       # this allocation has no possible witness
            if len(d) == 1:
                units.append(d[0])
            live.append(d)
        if not live:
            return False          # a total order extending R would work
        if units:
            for x, y in units:
                q = add_arc(R, x, y)
                if q is None:
                    return True   # two necessary arcs imply a directed cycle
                R = q
            return visit(R, live)
        best = min(map(len, live))
        freq = Counter()
        for c in live:
            if len(c) <= best + 2:
                for x, y in c:
                    freq[min(x, y), max(x, y)] += 1 << (best+2-len(c))
        x, y = max(freq, key=lambda o: freq[o])
        Rxy, Ryx = add_arc(R, x, y), add_arc(R, y, x)
        assert Rxy is not None and Ryx is not None
        return visit(Rxy, live) and visit(Ryx, live)
    verdict = visit(R, F)
    return verdict, nodes

def main():
    A = tuple(all_allocations())
    assert len(A) == 40824
    cases = [((1,1,1,1,4),0), ((1,1,6),0), ((1,3,4),0), ((1,3,4),1)]
    for shape, t in cases:
        R, F = arcs_for(shape, t, A)
        ok, nodes = refute(R, F)
        assert ok, (shape, t)
        print(f"{shape} top={t} classes={len(R)} clauses={len(F)} nodes={nodes}")
    print("PASS: all four A4 mixed-action cases refuted")

if __name__ == "__main__":
    main()
