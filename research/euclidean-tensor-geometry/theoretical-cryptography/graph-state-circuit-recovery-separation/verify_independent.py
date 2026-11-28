#!/usr/bin/env python3
"""Literal columns of [I|A] for every admissible circuit; direct row space."""
from itertools import combinations, product

BASE = ("03", "04", "05", "13", "15", "24", "25")
NEAR = (1, 2, 3, 4)


def graph(r):
    m = 6+r
    edges = {tuple(map(int, e)) for e in BASE}
    edges.update((i, j) for i in NEAR for j in range(6, m))
    edges.update(combinations(range(6, m),2))
    return [[int(tuple(sorted((i, j))) in edges) for j in range(m)]
            for i in range(m)]


def as_set(mask, n):
    return frozenset(i for i in range(n) if mask >> i & 1)


def mask(vertices):
    return sum(1 << i for i in vertices)


def linrank(vs):
    # Literal column rank, by an independent elimination implementation.
    # Pivot on the least set bit of the first nonzero remaining column.
    vs = list(vs)
    piv = 0
    while piv < len(vs):
        nz = next((j for j in range(piv,len(vs)) if vs[j]),None)
        if nz is None:
            break
        vs[nz], vs[piv] = vs[piv], vs[nz]
        bit = vs[piv] & -vs[piv]
        for j in range(piv+1,len(vs)):
            if vs[j] & bit:
                vs[j] ^= vs[piv]
        piv += 1
    return piv


def literal_circuits(a):
    n = len(a)
    col = [(1 << i, mask(j for j in range(n) if a[j][i])) for i in range(n)]
    all_min = []
    # A dependent admissible set is a circuit iff every one-column
    # deletion is independent. We first filter by the XOR of its columns:
    # this must vanish for every minimal relation over F_2.
    for tags in product((0,1,2), repeat=n):
        cs = [(i, col[i][u-1]) for i,u in enumerate(tags) if u]
        if not cs:
            continue
        total = 0
        for _, x in cs:
            total ^= x
        if total:
            continue
        if linrank(x for _, x in cs) != len(cs)-1:
            continue
        all_min.append(frozenset(i for i,_ in cs))
    return all_min, 3**n


def supported_space(a):
    n = len(a)
    out = []
    # Form the literal row span of [I|A]. Length is small here.
    for bits in product((0,1), repeat=n):
        av = tuple(sum(a[i][j]*bits[j] for j in range(n)) % 2
                   for i in range(n))
        supp = frozenset(i for i,(x,y) in enumerate(zip(bits,av)) if x or y)
        out.append((supp,tuple(zip(bits,av))))
    return out


def ms(sets):
    return frozenset(x for x in sets if not any(y < x for y in sets))


def disp(s):
    return tuple(sorted("".join(map(str,t)) for t in map(sorted,s)))


def test():
    base, total_tags = None, 0
    rows = []
    print("Explicit circuits/direct projection, (r, admissible columns tested,"
          " circuit count, support count, QAS dealers, bad minimal-set/dealer pairs):")
    for r in range(1,6):
        a = graph(r)
        c, ct = literal_circuits(a)
        total_tags += ct
        n = len(a)
        w = supported_space(a)
        supports = frozenset(s for s, v in w if s and (1,1) not in v)
        T = frozenset(range(6,n))

        def expand(S):
            return (S-{6}) | (T if 6 in S else frozenset())

        if r == 1:
            base = supports
            # Compare all ordered first/second-coordinate supports
            # to the displayed base relation table, not only its sizes.
            base_pairs = {
                ("".join(str(i) for i,(x,_) in enumerate(v) if x),
                 "".join(str(i) for i,(_,y) in enumerate(v) if y))
                for s,v in w if s and (1,1) not in v
            }
            words = ("012/5 5/012 3/016 01/46 02/36 4/026 0/345 "
                     "345/0 12/34 34/12 1/356 45/16 35/26 2/456 "
                     "06/125 1256/0 0346/5 56/034 6/1234 12346/ "
                     "23/0145 14/0235 0135/24 0245/13 136/0245 "
                     "246/0135 02356/14 01456/23")
            assert base_pairs == {tuple(w.split("/")) for w in words.split()}
        else:
            assert supports == {expand(S) for S in base}
        bad = frozenset({1,3}) | T
        assert {v[0] for s,v in w if s <= bad | {0}} == {(0,0),(0,1)}
        qas_count, failures = 0, 0
        for d in range(n):
            family = ms({S-{d} for S in c if d in S})
            assert family == ms({S-{d} for S in supports if d in S})
            # Equality for each entire family, after removing this dealer.
            old = min(d,6)
            assert family == ms({expand(S)-{d} for S in base if old in S})
            if d == 0:
                assert bad in family
            qas = bool(family) and all(A & B for A in family for B in family)
            qas_count += qas
            assert qas == (r > 1 or d != 6)
            if r == 1 and d in (0,1):
                assert disp(family) == {0: ("125","136","146","236","246","345"),
                                       1: ("025","036","046","234","356","456")}[d]
            if qas:
                for S in family:
                    D = {v[d] for sup,v in w if sup <= S | {d}}
                    failures += len(D) != 4
        row = (r,ct,len(c),len(supports),qas_count,failures)
        rows.append(row)
        print(row)
    assert rows == [(1,2187,28,16,6,24), (2,6561,46,16,8,24),
                    (3,19683,82,16,9,24), (4,59049,154,16,10,24),
                    (5,177147,298,16,11,24)]
    print(f"{total_tags} literal admissible column subsets;"
          " support-family substitution exact.")


if __name__ == "__main__":
    test()
