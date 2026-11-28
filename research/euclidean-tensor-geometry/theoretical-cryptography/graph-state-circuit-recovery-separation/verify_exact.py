#!/usr/bin/env python3
"""Generate small unlabelled graphs from scratch, then parity/cut-rank tests."""
from itertools import groupby, permutations, product


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            i = row.bit_length()
            if i not in pivots:
                pivots[i] = row
                break
            row ^= pivots[i]
    return len(pivots)


def decode(n, k):
    masks = [0]*n
    shift = 0
    for j in range(1, n):
        for i in range(j):
            if (k >> shift) & 1:
                masks[j] |= 1 << i
                masks[i] |= 1 << j
            shift += 1
    return tuple(masks)


def canonical(mask):
    order = sorted(range(len(mask)), key=lambda i: mask[i].bit_count())
    blocks = [tuple(g) for _, g in
              groupby(order, key=lambda i: mask[i].bit_count())]
    pairs = [(i, j) for j in range(1, len(mask)) for i in range(j)]
    best = None
    for permblocks in product(*(tuple(permutations(b)) for b in blocks)):
        p = sum(permblocks, ())
        k = sum(((mask[p[i]] >> p[j]) & 1) << s
                for s, (i, j) in enumerate(pairs))
        if best is None or k < best:
            best = k
    return best


def graph_layers(N):
    prev = [(0,)]
    yield 1, prev
    for n in range(2, N+1):
        forms = set()
        for g in prev:
            for adj in range(1 << (n-1)):
                child = tuple(row | ((adj >> i & 1) << (n-1))
                              for i, row in enumerate(g))+(adj,)
                forms.add(canonical(child))
        prev = [decode(n, k) for k in sorted(forms)]
        yield n, prev


def connected(g):
    old, reach = 0, 1
    while old != reach:
        old = reach
        for i, neigh in enumerate(g):
            if old >> i & 1:
                reach |= neigh
    return reach == (1 << len(g))-1


def bipartite(g):
    colors = {0: 0}
    queue = [0]
    for v in queue:
        for u in range(len(g)):
            if g[v] >> u & 1:
                if u not in colors:
                    colors[u] = 1-colors[v]
                    queue.append(u)
                elif colors[v] == colors[u]:
                    return False
    return True


def antichain(supports):
    return {a for a in supports if not any(b != a and (a & b) == b
                                          for b in supports)}


def data(g):
    n = len(g)
    allv = (1 << n)-1
    images = [0]*(allv+1)
    cuts = []
    for a in range(allv+1):
        low = a & -a
        if low:
            images[a] = images[a ^ low] ^ g[low.bit_length()-1]
        cuts.append(rank(row & (allv ^ a)
                         for v, row in enumerate(g) if a >> v & 1))
    par_support = {a|b for a, b in enumerate(images) if a and not (a & b)}
    ans = []
    two_colorable = bipartite(g)
    for d in range(n):
        D, P = 1 << d, allv ^ (1 << d)
        mins = antichain({s ^ D for s in par_support if s & D})
        qas = bool(mins) and all(a & b for a in mins for b in mins)
        inc = all(cuts[B] - cuts[B | D] == 1 for B in mins)
        eq = inc and all(any(B & m == m for m in mins)
                         for B in range(allv+1) if B & D == 0
                         and cuts[B] - cuts[B | D] == 1)
        dim = [1+cuts[A]-cuts[A|D] for A in range(allv+1) if A & D == 0]
        if two_colorable:
            assert qas == eq == (1 not in dim)
            assert all(0 <= j <= 2 for j in dim)
        ans.append((qas, inc, eq, mins))
    if two_colorable:
        assert all(x[2] for x in ans) == all(images[row] == 1 << i
                                            for i,row in enumerate(g))
    return ans


def main():
    expect_isomorphism = [None,1,2,4,11,34,156,1044]
    expect_conn = [None,1,1,2,6,21,112,853]
    table = []
    bgraphs = bchecks = 0
    print("Self-generated census; columns n, all graphs, connected,"
          " qas pairs, inclusion among qas, equality among qas,"
          " all-dealer qas graphs, fixed-dealer failure graphs,"
          " all-dealer-qas failure graphs:")
    for n, gs in graph_layers(7):
        cs = [g for g in gs if connected(g)]
        assert (len(gs), len(cs)) == (expect_isomorphism[n], expect_conn[n])
        if n == 1:
            continue
        nq = ni = ne = ng = nf = nfg = 0
        for g in cs:
            if bipartite(g):
                bgraphs += 1
                bchecks += n
            d = data(g)
            nq += sum(q for q,_,_,_ in d)
            ni += sum(q and i for q,i,_,_ in d)
            ne += sum(q and e for q,_,e,_ in d)
            glob = all(q for q,_,_,_ in d)
            fail = any(q and not i for q,i,_,_ in d)
            ng += glob
            nf += fail
            nfg += glob and fail
        row = (n,len(gs),len(cs),nq,ni,ne,ng,nf,nfg)
        print(row)
        table.append(row)
    assert [r[3:7] for r in table[:5]] == [(2,2,2,1),(3,3,3,1),
                                          (8,8,8,1),(29,29,29,1),
                                          (156,156,120,4)]
    assert table[-1] == (7,1044,853,1002,968,590,6,11,0)
    assert [r[-2] for r in table] == [0,0,0,0,0,11]
    assert all(r[-1] == 0 for r in table)
    print(f"Bipartite characterization checked on {bgraphs} connected graphs,"
          f" {bchecks} dealer positions.")


if __name__ == "__main__":
    main()
