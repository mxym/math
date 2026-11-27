"""Independent subspace incidence bitsets and normalized obstruction enumeration."""
from collections import Counter
from itertools import combinations


def mask(points):
    return sum(1 << x for x in set(points))


def rankbasis(vs):
    pivots = {}
    for v in vs:
        while v:
            j = v.bit_length()-1
            if j not in pivots:
                pivots[j] = v
                break
            v ^= pivots[j]
    return len(pivots)


def r(B):
    return B.bit_count().bit_length()-1


def all_planes(n):
    return sorted({1 | (1 << p) | (1 << q) | (1 << (p ^ q))
                    for p,q in combinations(range(1,1<<n),2)})


def all_hypers(n):
    return [mask(x for x in range(1 << n) if (a&x).bit_count() % 2 == 0)
            for a in range(1,1<<n)]


def cliques(neighbors, k, active, prefix=()):
    if not k:
        yield prefix
        return
    while active.bit_count() >= k:
        b = active & -active
        i = b.bit_length()-1
        active ^= b
        yield from cliques(neighbors, k-1, active & neighbors[i], prefix+(i,))


def check_n4():
    planes, hypers = all_planes(4), all_hypers(4)
    assert len(planes) == 35 and len(hypers) == 15
    adjacency = [mask(j for j,Q in enumerate(planes) if (P&Q).bit_count() == 2)
                 for P in planes]
    families = list(cliques(adjacency,7,(1<<len(planes))-1))
    assert len(families) == 30
    counts = Counter()
    pencilsets = set()
    for js in families:
        P = {planes[j] for j in js}
        H = {H for H in hypers if all(r(H&X) == 1 for X in P)}
        counts[len(H)] += 1
        if len(H) != 8:
            assert not H
            continue
        code = frozenset({1} | P | H)
        # Arbitrary order within each layer; groups are applied to these labels.
        labels = [1]+sorted(P)+sorted(H)
        assert set(labels) == code
        for a,X in enumerate(labels):
            for b,Y in enumerate(labels):
                assert r(X)+r(Y)-2*r(X&Y) == r(labels[a^b])
        pencilsets.add(code)
    assert counts == {0:15,8:15}
    print('independent n=4: 30 seven-plane cliques; compatible hyperplane counts', sorted(counts.items()))

    coordinate = set()
    for basis in combinations(range(1,16),4):
        if rankbasis(basis) != 4:
            continue
        subspaces = [1]
        points = {1:{0}}
        for v in basis:
            more = []
            for B in subspaces:
                U = points[B]
                W = U | {u^v for u in U}
                C = mask(W)
                points[C] = W
                more.append(C)
            subspaces += more
        coordinate.add(frozenset(subspaces))
    assert len(coordinate) == 840

    fano_products = set()
    sections = 0
    # For each distinguished line L, independently enumerate all binary
    # selections of lifts of the seven nonzero quotient vectors.
    for ell in range(1,16):
        reps = [x for x in range(16) if x < (x^ell)]
        assert len(reps) == 8 and reps[0] == 0
        q = {x: i for i,w in enumerate(reps) for x in (w,w^ell)}
        triples = sorted({tuple(sorted((i,j,q[reps[i]^reps[j]])))
                          for i,j in combinations(range(1,8),2)})
        assert len(triples) == 7
        ts = 0
        for selector in range(128):
            lift = [0]+[reps[i] ^ ((selector>>(i-1)&1)*ell) for i in range(1,8)]
            if any(lift[i]^lift[j]^lift[k] for i,j,k in triples):
                continue
            low = [1]+[mask((0,lift[i],lift[j],lift[k])) for i,j,k in triples]
            high = [P | mask(x^ell for x in range(16) if P>>x&1) for P in low]
            assert len(set(low+high)) == 16
            fano_products.add(frozenset(low+high))
            ts += 1
        assert ts == 8
        sections += ts
    assert sections == len(fano_products) == 120
    assert len(coordinate | fano_products | pencilsets) == 975
    print('independent n=4: 840 basis sets + 120 Fano lifts + 15 pencils = 975 distinct sets')


def check_n5():
    # Fix a shortest odd circuit in a four-space. Enumerate all choices of
    # the remaining layer, without distinguishing stars from triangles.
    E = {1,2,4,8,15}
    B = list(range(16,32))
    assert rankbasis(E) == 4
    profile = Counter()
    lower_shared = 32
    for k in range(4,17):
        for Bprime in combinations(B,k):
            if any((a^b) in E for a,b in combinations(Bprime,2)):
                continue
            S = E | set(Bprime)
            assert len(S) == 5+k
            D = {a^b for a,b in combinations(S,2)}
            assert not S & D
            absent = [mask(s for s in S if s^t not in S) for t in sorted(D)]
            shared = max((A&B).bit_count() for A,B in combinations(absent,2))
            assert shared >= 4   # distinct 3-space annihilators have <=3 common normals
            lower_shared = min(lower_shared,shared)
            profile[len(S)] += 1
    assert profile == {9:120,10:16}
    print('independent n=5: normalized noncoset layers', sorted(profile.items()),
          '; smallest maximum common-forced normals', lower_shared)


if __name__ == '__main__':
    check_n4()
    check_n5()
