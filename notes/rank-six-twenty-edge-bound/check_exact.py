"""Finite exact diagnostics for the written twenty-edge proof."""
from itertools import combinations, combinations_with_replacement
from math import comb


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def partitions(N, D, minimum=2, width=6):
    def rec(left, maximum, prefix):
        if left == 0:
            if len(prefix) >= width:
                yield prefix
            return
        for value in range(min(left, maximum), minimum-1, -1):
            yield from rec(left-value, value, prefix+(value,))
    return list(rec(N, D, ()))


def independent_partitions(N, D, minimum=2, width=6):
    # Counts of vertices of each possible degree, instead of sorted rows.
    out = []
    def rec(degree, left, counts):
        if degree == D+1:
            if left == 0 and sum(counts) >= width:
                out.append(tuple(d for d, n in zip(range(minimum, D+1), counts) for _ in range(n)))
            return
        for n in range(left//degree+1):
            rec(degree+1, left-degree*n, counts+(n,))
    rec(minimum, N, ())
    return out


def energy(pattern):
    return sum(comb(d, 2) for d in pattern)


def degree_tables():
    for N, D, bound in ((17, 4, 18), (18, 5, 24), (19, 6, 29)):
        ps = partitions(N, D)
        require(set(ps) == {tuple(sorted(p, reverse=True)) for p in independent_partitions(N, D)},
                'independent degree generators')
        require(max(map(energy, ps)) == bound, 'complete energy maximum')
        print(f'N={N}, degree cap={D}, {len(ps)} patterns: maximum part energy {bound} PASS')
    ps = partitions(19, 6)
    require({u: max(energy(p) for p in ps if len(p) == u) for u in range(6, 10)}
            == {6: 29, 7: 23, 8: 17, 9: 11}, 'width table')
    require(max(energy(p) for p in ps if max(p) <= 5) == 26, 'no-degree-six maximum')
    # Expand six-part choices. A single low-degree part can only leave
    # energy exactly 171, hence zero intersection excess and five high
    # blocks; two low-degree parts cannot meet the pair requirement.
    count = 0
    for ix in combinations_with_replacement(range(len(ps)), 6):
        selected = [ps[i] for i in ix]
        S = sum(map(energy, selected))
        if S < 171:
            continue
        require(S <= 174, 'small excess')
        low = sum(max(p) <= 5 for p in selected)
        if low:
            require(low == 1 and S == 171 and 30-comb(5, 2) > 19,
                    'linear five-high-block contradiction')
        count += 1
    require(count > 0, 'nonempty diagnostic domain')
    # Independent damaged maximum must be rejected.
    require(30 != max(map(energy, ps)), 'damaged energy negative control')
    print(f'All six-part degree choices with S>=171 checked: {count} PASS')
    ps20 = partitions(20, 7)
    require({u: max(energy(p) for p in ps20 if len(p) == u) for u in range(6, 11)}
            == {6: 35, 7: 29, 8: 22, 9: 14, 10: 10}, 'twenty-edge width table')
    require(5*35+14 < comb(20, 2), 'complete next-case width bound')
    require(6*35-2*(35-22) < 190, 'at most one width-eight part')
    require(6*35-(35-22)-2*(35-29) < 190, 'width-eight and width-seven budget')
    require(6*35-4*(35-29) < 190, 'at most three width-seven parts')
    print('Complete twenty-edge width restriction and degree-pattern budgets PASS')


def excess_partitions(total):
    def rec(left, maximum, prefix):
        if left == 0:
            yield prefix
            return
        for value in range(min(left, maximum), 0, -1):
            yield from rec(left-value, value, prefix+(value,))
    return list(rec(total, total, ()))


def overlap_budget():
    supports = list(combinations(range(6), 4))
    pair_counts = {p: sum(set(p) <= set(s) for s in supports)
                   for p in combinations(range(6), 2)}
    require(len(supports) == 15 and set(pair_counts.values()) == {6}, 'four-subset multiplicities')
    require(15*8 == 6*20, 'summed codegree budget')
    for b in range(20):
        require(comb(b, 2) >= b-1, 'integer codegree inequality')
    for I in range(4):
        for profile in excess_partitions(I):
            Q = sum(j*(j+1)//2 for j in profile)
            if Q >= 5:
                require(I == 3 and profile == (3,) and Q == 6, 'forced exceptional edge pair')
    for special in supports:
        outside = set(range(6))-set(special)
        for inside in combinations(special, 2):
            chosen = outside | set(inside)
            capacity = sum(1+int(i in special and j in special) for i, j in combinations(sorted(chosen), 2))
            require(len(chosen) == 4 and capacity == 7 and capacity < 8,
                    'exceptional-support contradiction')
    print('Four-subset budgets, every excess profile I<=3 and every exceptional support PASS')


def appendix_checks():
    ps = partitions(11, 3, minimum=1, width=5)
    other = independent_partitions(11, 3, minimum=1, width=5)
    require(set(ps) == {tuple(sorted(p, reverse=True)) for p in other}, 'appendix partition generators')
    require(max(map(energy, ps)) == 9 and 6*9 < comb(11, 2), 'eleven-edge energy contradiction')
    for d in range(1, 5):
        require(comb(d, 2) == d-1+int(d == 3)+3*int(d == 4), 'appendix exact degree identity')
    survivors = []
    for x4 in range(7):
        for x3 in range(19-2*x4):
            for n in range(30, 73):
                S = 72-n+x3+3*x4
                if S >= 66:
                    survivors.append((x3, x4, n, S))
    require(survivors == [(6, 6, 30, 66)], 'appendix forced equality')

    # Mathematical data from ABW Theorem 2.7, equation (7), not a new construction.
    rows = ['111111', '444114', '125334', '241535', '545421',
            '222211', '553315', '213444', '351224', '333131',
            '143252', '255153', '514233']
    edges = [tuple(map(int, row)) for row in rows]
    require(len(set(edges)) == 13 and all(any(a == b for a, b in zip(e, f))
                                        for e, f in combinations(edges, 2)), 'ABW boundary intersection')
    vertices = sorted({(c, v) for edge in edges for c, v in enumerate(edge)})
    masks = [sum(1 << i for i, edge in enumerate(edges) if edge[c] == v) for c, v in vertices]
    full = (1 << 13)-1
    checked = 0
    for subset in combinations(range(len(vertices)), 4):
        union = 0
        for i in subset:
            union |= masks[i]
        require(union != full, 'ABW boundary has no four-cover')
        checked += 1
    side = [i for i, (c, _) in enumerate(vertices) if c == 0]
    total = 0
    for i in side:
        total |= masks[i]
    require(len(side) == 5 and total == full and checked == comb(30, 4), 'ABW five-cover boundary')
    print(f'Appendix identities and published thirteen-edge boundary: {checked} four-subsets PASS')


if __name__ == '__main__':
    degree_tables()
    overlap_budget()
    appendix_checks()
