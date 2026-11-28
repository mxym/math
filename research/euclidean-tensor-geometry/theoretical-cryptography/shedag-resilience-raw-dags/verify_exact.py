#!/usr/bin/env python3
"""Definition-level finite checks: Floyd closure, all subsets, histogram and truncated lists."""
from itertools import combinations


def dag(n, flags):
    return [(u, v) for k, (u, v) in enumerate(combinations(range(n), 2))
            if flags >> k & 1]


def closure(n, edges):
    a = [1 << i for i in range(n)]
    for u, v in edges:
        a[v] |= 1 << u
    for k in range(n):
        for v in range(n):
            if a[v] >> k & 1:
                a[v] |= a[k]
    return a


def depth(a, s):
    return max((x & s).bit_count() for i, x in enumerate(a) if s >> i & 1)


def values(a):
    ans = [-1, -1]
    maximizers = [set(), set()]
    for s in range(1, 1 << len(a)):
        d = depth(a, s)
        for aa in (1, 2):
            v = s.bit_count() - max(aa, d)
            if v > ans[aa - 1]:
                ans[aa - 1] = v
                maximizers[aa - 1] = {s}
            elif v == ans[aa - 1]:
                maximizers[aa - 1].add(s)
    return ans, maximizers


def scan(c, limit):
    n = len(c)
    out = {}
    for aa in (1, 2):
        out[aa] = max((s.bit_count() - max(aa, x), s)
                      for x in range(1, limit + 1)
                      if (s := sum(1 << i for i, cc in enumerate(c) if cc <= x)))
    return out


def truncated(n, edges, limit):
    # Keep the largest IDs to test an order other than the topological one.
    lists = [{i} for i in range(n)]
    for u, v in edges:  # Lexicographic order of (u,v): the u list is already complete.
        lists[v] = set(sorted(lists[v] | lists[u], reverse=True)[:limit])
    return [len(s) for s in lists]


def run():
    instances = subsets = caps = ideals = 0
    strict_approx_cases = 0
    for n in range(2, 6):
        for flags in range(1 << (n * (n - 1) // 2)):
            edges = dag(n, flags)
            a = closure(n, edges)
            c = [x.bit_count() for x in a]
            ans, opts = values(a)
            hist = scan(c, n)
            for aa in (1, 2):
                got, w = hist[aa]
                assert got == ans[aa - 1] and w in opts[aa - 1]
                threshold_sets = {sum(1 << i for i, p in enumerate(c) if p <= x)
                                  for x in range(1, n + 1)}
                for s in opts[aa - 1]:
                    if all(not (a[i] & ~s) for i in range(n) if s >> i & 1):
                        assert s in threshold_sets
                        ideals += 1
            for k in range(1, n + 1):
                cap = truncated(n, edges, k + 1)
                assert cap == [min(x, k + 1) for x in c]
                for aa, (v, w) in scan(cap, k).items():
                    assert (v >= n - k) == (ans[aa - 1] >= n - k)
                    if v >= n - k:
                        assert v == ans[aa - 1] and w in opts[aa - 1]
                caps += 1
            # Force both signs of relative perturbation (eta=1/3), and restore isotonicity.
            h = [max(1, (2 * x + 2) // 3) if i % 2 else min(n, (4 * x) // 3)
                 for i, x in enumerate(c)]
            b = [max(h[i] for i in range(n) if a[v] >> i & 1) for v in range(n)]
            assert all(2 * x <= 3 * y <= 4 * x for x, y in zip(c, b))
            for aa, (v, w) in scan(b, n).items():
                dh, true = n - v, n - ans[aa - 1]
                dw = n - w.bit_count() + max(aa, depth(a, w))
                assert 2 * true <= 3 * dh <= 4 * true and dw <= 2 * true
                assert all(not (a[i] & ~w) for i in range(n) if w >> i & 1)
                strict_approx_cases += int(dw > true)
            instances += 1
            subsets += (1 << n) - 1
    # Negative controls for three distinct printed/algorithmic issues.
    a = closure(3, [(0, 1), (1, 2)])
    n, s = 3, 0b101
    assert s.bit_count() - max(2, depth(a, s)) == values(a)[0][1] == 0
    assert s.bit_count() - max(max(2, a[i].bit_count()) for i in range(n) if s >> i & 1) == -1
    assert s not in {sum(1 << i for i in range(n) if a[i].bit_count() <= x)
                     for x in range(1, n + 1)}
    assert values(closure(3, []))[0][0] == 2 < 3  # Literal Algorithm 2 output = 3.
    a = closure(4, [(0, 1), (0, 2), (1, 3), (2, 3)])
    assert a[-1].bit_count() == 4 < 1 + a[1].bit_count() + a[2].bit_count()
    assert strict_approx_cases > 0
    print(f"PASS definitions: {instances} DAGs, {subsets} subsets, {ideals} maximizing ideals")
    print(f"PASS capped exact: {caps} decision caps; {strict_approx_cases} non-optimal approximate witnesses covered")
    print("PASS negative controls: Algorithm 2 offset, non-ideal entropic optimum, diamond overlap")


if __name__ == "__main__":
    run()
