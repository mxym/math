#!/usr/bin/env python3
"""Independent score oracle by directed out-core peeling; explicit reductions and sketches."""
from itertools import combinations, product
from collections import deque
from math import comb
from fractions import Fraction


def ancestors(n, edges):
    pred = [[] for _ in range(n)]
    for u, v in edges:
        pred[v].append(u)
    rows = []
    for v in range(n):
        reached = {v}
        todo = [v]
        while todo:
            for u in pred[todo.pop()]:
                if u not in reached:
                    reached.add(u)
                    todo.append(u)
        rows.append(reached)
    return rows


def core_scores(a):
    # For target r, each v in a feasible S has >= r out-neighbors inside S
    # in the digraph v->u iff u is NOT a closed ancestor of v. Any feasible S
    # survives the peeling, so the largest survivor maximizes its cardinality.
    n = len(a)
    arc = [set(range(n)) - row for row in a]
    rev = [set() for _ in a]
    for v, out in enumerate(arc):
        for u in out:
            rev[u].add(v)
    ans = [0, 0]
    for r in range(1, n):
        degree = list(map(len, arc))
        live = set(range(n))
        q = deque(v for v in live if degree[v] < r)
        while q:
            v = q.popleft()
            live.remove(v)
            for u in rev[v] & live:
                degree[u] -= 1
                if degree[u] == r - 1:
                    q.append(u)
        if not live:
            break
        ans[0] = r
        if len(live) >= r + 2:  # r2>=r requires in addition |S|>=r+2.
            ans[1] = r
    return tuple(ans)


def pad(n, edges, q):
    assert 2 <= q <= n
    p = n + q - 2
    return n + 2 * q - 1, edges + [(u, p) for u in range(n, p)] + [
        (p, v) for v in range(p + 1, p + q + 1)]


def encode(a, b, d):
    m = len(a)
    c, dummy, sinks = m, m + d, m + 2 * d
    edges = [(j, c+k) for j in range(m) for k in range(d) if b[j] & 1 << k]
    edges += [(c+k if a[i] & 1 << k else dummy+k, sinks+i)
              for k in range(d) for i in range(m)]
    return 2*m + 2*d, edges


def rank_check():
    # Finite dyadic union/count checks with repeated ranks and genuine saturation.
    tests = 0
    n, jmax = 4, 2
    for flags in range(1 << comb(n, 2)):
        edges = [e for i, e in enumerate(combinations(range(n), 2)) if flags >> i & 1]
        ref_graph = ancestors(n, edges)
        for h in product(range(1 << jmax), repeat=n):
            for cap in (2, 3):
                keep = [{(rank, i)} for i, rank in enumerate(h)]
                for u, v in edges:
                    keep[v] = set(sorted(keep[v] | keep[u])[:cap])
                for v in range(n):
                    for j in range(jmax + 1):
                        t = 1 << (jmax - j)
                        observed = sum(rank < t for rank, _ in keep[v])
                        expected = sum(h[u] < t for u in ref_graph[v])
                        assert observed == min(expected, cap)
                tests += 1
    return tests


def binomial_check():
    # The rank-count mean is exact and the first unsaturated scale transfer
    # depends on the joint good event, not independent tests at different j.
    moments = cases = 0
    for c in range(1, 13):
        jj = (c - 1).bit_length()
        for j in range(jj + 1):
            p = Fraction(1, 1 << j)
            pmf = [comb(c, x) * p**x * (1-p)**(c-x) for x in range(c+1)]
            assert sum(pmf) == 1 and sum(x * w for x, w in enumerate(pmf)) == c*p
            moments += 1
    # Direct enumeration of correlated rank choices on one set.
    for c in range(3, 7):
        jj = (c - 1).bit_length()
        powers = [1 << (jj-j) for j in range(jj+1)]
        for h in product(range(1 << jj), repeat=c):
            x = [sum(y < t for y in h) for t in powers]
            for cap in range(3, c+1):
                good = all((4*c < cap << j or 3*abs((z << j)-c) <= c)
                           and (2*c >= cap << j or z < cap)
                           for j, z in enumerate(x))
                if good:
                    j = next(j for j, z in enumerate(x) if z < cap)
                    assert j > 0 and 4*c >= cap << j
                    assert 2*c <= 3*(x[j] << j) <= 4*c
                    cases += 1
    assert cases > 0
    return moments, cases


def run():
    cases = hse_cases = yes = sparse = 0
    for n in range(2, 5):
        ee = list(combinations(range(n), 2))
        for f in range(1 << len(ee)):
            e = [x for i, x in enumerate(ee) if f >> i & 1]
            cmax = max(map(len, ancestors(n, e)))
            for q in range(2, n+1):
                nn, de = pad(n, e, q)
                oracle = core_scores(ancestors(nn, de))
                for r in oracle:
                    assert (r == nn - q) == (cmax <= q)
                    if cmax == q+1:
                        assert r == nn - q - 1
                cases += 1
    for m, d in ((1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (3, 1), (3, 2)):
        q = m+d
        for lists in product(range(1 << d), repeat=2*m):
            a, b = lists[:m], lists[m:]
            answer = any(all(x & y for y in b) for x in a)
            n, edges = encode(a, b, d)
            nn, e = pad(n, edges, q)
            assert nn == 4*m+4*d-1
            assert len(e) == m*d + sum(y.bit_count() for y in b) + 2*q-2
            z = max(0, len(e)-nn)
            assert len(e) <= nn+z
            r = nn+z-q-int(answer)
            assert core_scores(ancestors(nn+z, e)) == (r, r)
            hse_cases += 1
            yes += answer
            sparse += int(z > 0)
    # Ensure the isolate-padding branch is tested when small exhaustive families
    # happen to have insufficient edge count to trigger it.
    m, d = 5, 7
    for a in ((0,)*m, ((1 << d)-1,)*m):
        b = ((1 << d)-1,)*m
        n, edges = encode(a, b, d)
        nn, e = pad(n, edges, m+d)
        z = len(e)-nn
        assert z > 0
        r = nn+z-(m+d)-int(a[0] != 0)
        assert core_scores(ancestors(nn+z, e)) == (r, r)
        sparse += 1
    # Omit the balancing dummies: identical reach-to-B success then no longer
    # forces the prescribed c(a_i)=d+m+1. The example tests the actual failure.
    n, e = encode((1,), (1,), d=2)
    e = [(u, v) for u, v in e if u != 1+2+1]
    nn, e = pad(n, e, 3)
    assert core_scores(ancestors(nn, e)) == (nn-3, nn-3)
    print(f"PASS core oracle: {cases} general padding instances")
    print(f"PASS HSE: {hse_cases} exhaustive instances ({yes} YES), {sparse} positive isolate-padding cases, 1 dummy negative control")
    print(f"PASS finite ranks: {rank_check()} union/saturation instances")
    m, g = binomial_check()
    print(f"PASS binomial: {m} exact means, {g} correlated good-rank checkpoints")


if __name__ == "__main__":
    run()
