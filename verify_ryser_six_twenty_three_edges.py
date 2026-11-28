#!/usr/bin/env python3
"""Exact integers only. Verifies the finite claims in RyserSixTwentyThreeEdges.md."""
from functools import lru_cache
from itertools import combinations
from math import comb


def require(proposition, detail):
    if not proposition:
        raise RuntimeError(detail)


def integer_partitions(n, length, lo, hi):
    if not length:
        if not n:
            yield ()
        return
    for x in range(lo, min(hi, n // length) + 1):
        for p in integer_partitions(n - x, length - 1, x, hi):
            yield (x,) + p


def confirm_eight_edge_structure():
    # Rows are 0,...,7. A degree-three vertex uses a triple of rows.
    # Every two triples meet, and every row is in some triple. There is at
    # most one such vertex per part and each remaining block has size <= 2.
    all_rows = (1 << 8) - 1
    pairs = list(combinations(range(8), 2))
    all_pairs = (1 << len(pairs)) - 1
    pair_bit = {p: 1 << i for i, p in enumerate(pairs)}
    triples = [(sum(1 << x for x in t),
                sum(pair_bit[p] for p in combinations(t, 2)))
               for t in combinations(range(8), 3)]

    @lru_cache(None)
    def matchings(available, allowed, k):
        if k == 0:
            return (0,)
        if available.bit_count() < 2*k:
            return ()
        first = available & -available
        v = first.bit_length() - 1
        rest = available ^ first
        choices = list(matchings(rest, allowed, k))
        for w in range(v + 1, 8):
            bit = pair_bit[v, w]
            if (rest & (1 << w)) and (allowed & bit):
                for rem in matchings(rest ^ (1 << w), allowed, k - 1):
                    choices.append(rem | bit)
        return tuple(choices)

    def audit(t, repeat_cap):
        counts = [0, 0, 0]  # tested complete covers, zero-duplicate covers, completions
        def complete(stars, missing, i):
            if i == len(stars):
                return bool(matchings(all_rows, missing, 4))
            return any(complete(stars, missing ^ extra, i + 1)
                       for extra in matchings(all_rows ^ stars[i], missing, 2))

        def visit(j0, stars, occupied, covered, repeats):
            if len(stars) == t:
                if occupied != all_rows:
                    return
                counts[0] += 1
                counts[1] += (repeats == 0)
                if t == 5 and repeats == 1:
                    # Need all fourteen remaining pair incidences; hence no
                    # edge pair can be used twice by the six matchings.
                    require((all_pairs ^ covered).bit_count() == 14, covered)
                    counts[2] += complete(stars, all_pairs ^ covered, 0)
                return
            for j in range(j0, len(triples)):
                s, p = triples[j]
                r = repeats + (p & covered).bit_count()
                if r <= repeat_cap and all(s & prev for prev in stars):
                    visit(j + 1, stars + (s,), occupied | s, covered | p, r)

        # Relabel rows to make one triple the lexicographically first triple.
        # Equal triples are impossible under our repeat caps (0 or 1).
        s, p = triples[0]
        visit(1, (s,), s, p, 0)
        return tuple(counts)

    a, b, c = audit(4, 0), audit(5, 1), audit(6, 0)
    require((a, b, c) == ((0, 0, 0), (900, 0, 0), (0, 0, 0)), (a, b, c))
    print("8-edge triples: t=4 0; t=5 900, completions 0; linear t=6 0")


def residual_sums(m, singletons):
    def types(min_length):
        return {
            (p.count(1), sum(comb(x, 2) for x in p), p.count(5))
            for k in range(min_length, m+1)
            for p in integer_partitions(m, k, 1, m-9)
            if p.count(1) <= singletons
            and all(sum(p[-j:]) <= m-g for j, g in ((2,5), (3,3), (4,1)))
        }
    base, other = types(5), types(6)
    for _ in range(5):
        base = {(a+b, s+t, u+v) for a, s, u in base for b, t, v in other
                if a+b <= singletons}
    return base


def confirm_residual_degree():
    a = residual_sums(13, 10)
    b = residual_sums(14, 9)
    d = sorted(x for x in b if x[1] >= 91)
    require(max(x[1] for x in a) == 70, max(x[1] for x in a))
    require(d == [(8,91,6), (9,91,5), (9,91,6), (9,92,6)], d)
    print("small one-vertex residuals: m=13 S<=70; m=14 survivors", d)


def row_minima(n, x, part):
    lows = [max(0, x+y-n+9) for y in part]
    ups = [0 if x == y == 2 else min(x,y)-1 for y in part]
    if any(low > up for low, up in zip(lows, ups)):
        return None, None
    # Separable convex objective: the next unit at c costs c.
    current = lows[:]
    greedy = None
    if sum(current) <= x <= sum(ups):
        for _ in range(x-sum(current)):
            j = min((j for j in range(len(current)) if current[j] < ups[j]),
                    key=current.__getitem__)
            current[j] += 1
        greedy = sum(comb(c, 2) for c in current)

    # Independent bounded integer composition DP.
    tab = {0:0}
    for a, b in zip(lows, ups):
        new = {}
        for t, val in tab.items():
            for q in range(a, min(b,x-t)+1):
                v = val+comb(q,2)
                new[t+q] = min(v, new.get(t+q, v))
        tab = new
    return greedy, tab.get(x)


def main_profiles(n):
    pats = sorted(
        (sum(comb(x,2) for x in p), 2*p.count(2), sum(x for x in p if x >= 4), p)
        for k in range(6,n//2+1) for p in integer_partitions(n,k,2,n-15)
        if sum(p[-2:]) <= n-9
    )
    K = len(pats)
    need = comb(n,2)
    if not K:
        return K,0,0,None

    @lru_cache(None)
    def row(x, p):
        g, dp = row_minima(n,x,p)
        require(g == dp, (n, x, p, g, dp))
        return g

    def matrix(a, b):
        u = [row(x,b) for x in a]
        v = [row(y,a) for y in b]
        if None in u or None in v:
            return None
        return max(sum(u),sum(v))

    B = [[matrix(a[-1],b[-1]) for b in pats] for a in pats]
    count = valid = 0
    best = None
    def visit(t, d2, h, s, b):
        nonlocal count, valid, best
        left = 6-len(t)
        if s + left*pats[-1][0] < need:
            return
        if not left:
            if h < 3*n:
                return
            count += 1
            if b is None:
                return
            valid += 1
            f = 4*(s-need)-2*b
            best = f if best is None else max(best,f)
            return
        for i in range(t[-1] if t else 0,K):
            w, a, k, _ = pats[i]
            if d2+a > n:
                continue
            costs = [B[i][j] for j in t]
            nb = None if b is None or None in costs else b+sum(costs)
            visit(t+(i,),d2+a,h+k,s+w,nb)

    visit((),0,0,0,0)
    return K,count,valid,best


def main():
    confirm_eight_edge_structure()
    confirm_residual_degree()
    table = {n:main_profiles(n) for n in range(12,23)}
    expected = {n:(0,0,0,None) for n in range(12,18)}
    expected.update({18:(4,0,0,None), 19:(9,0,0,None), 20:(22,0,0,None),
                     21:(35,0,0,None), 22:(57,171,171,-10)})
    require(table == expected, table)
    for n, r in table.items():
        print(n, *r)
        require(r[-1] is None or r[-1] < 0, (n,r))
    print("PASS: all at most 22 edges excluded")


if __name__ == "__main__":
    main()
