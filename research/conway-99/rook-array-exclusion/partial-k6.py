"""Exact partial K6 triangle-array obstruction, using only the Python standard library."""
from itertools import combinations, product


def mask(xs):
    return sum(1 << i for i in xs)


def check(missing):
    missing = tuple(map(frozenset, missing))
    edges = [frozenset(e) for e in combinations(range(6), 2) if frozenset(e) not in missing]
    m, n = len(missing), len(edges)
    dis = [mask(j for j, f in enumerate(edges) if not e & f) for e in edges]
    grids = [mask(t) for t in combinations(range(n), 3)
             if all(not edges[i] & edges[j] for i, j in combinations(t, 2))]
    stars = [mask(i for i, f in enumerate(edges) if a in f) for a in range(6)]
    specials = [mask(i for i, f in enumerate(edges) if not e & f) for e in missing]
    words = stars + specials
    assert len(set(words)) == len(words)
    assert set(words) == {w for w in range(1 << n) if all((w & g).bit_count() == 1 for g in grids)}
    off = set(range(6)) - set().union(*missing)
    # A pair of disjoint present fibers complementary to each e certifies population 3.
    for e in missing:
        assert any(not (f & g) and len(f | g | e) == 6 for f, g in combinations(edges, 2))
    # Each ordinary type's neighbor count is uniquely recovered by a triangle of present edges.
    idx = {e:i for i,e in enumerate(edges)}
    tri = []
    for a in range(6):
        b, c = next((b,c) for b,c in combinations(set(range(6)) - {a}, 2)
                    if all(frozenset(h) in idx for h in ((a,b),(a,c),(b,c))))
        tri.append(tuple(idx[frozenset(h)] for h in ((a,b),(a,c),(b,c))))
    counts = []
    for j, w in enumerate(words):
        deg = 14 - w.bit_count()
        demands = [6 - 3*((w >> i) & 1) - (w & dis[i]).bit_count() for i in range(n)]
        num = 0
        for v in product(range(deg + 1), repeat=m):
            rhs = [demands[i] - sum(x for x, s in zip(v, specials) if (s >> i) & 1) for i in range(n)]
            twice = [rhs[a]+rhs[b]-rhs[c] for a,b,c in tri]
            if any(x<0 or x%2 for x in twice): continue
            h = tuple(x//2 for x in twice)
            if sum(h)+sum(v)!=deg: continue
            if any(sum(h[k] for k in f)!=rhs[i] for i,f in enumerate(edges)): continue
            num += 1
            if j in off: assert sum(v)>=1
            if j>=6: assert all(h[k]<=1 for k in off)
        counts.append(num)
    assert all(counts) and 9*len(off)>3*m*len(off)
    print('missing',tuple(tuple(sorted(e))for e in missing),'grids',len(grids),'types',len(words),
          'integral rows by type',counts,'demand',9*len(off),'capacity',3*m*len(off))


if __name__=='__main__':
    check(((0,1),))
    check(((0,1),(2,3)))
    check(((0,1),(0,2)))
