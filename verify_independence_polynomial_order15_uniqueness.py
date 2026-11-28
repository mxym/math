#!/usr/bin/env python3
"""Integer checker for the order-15 classification and fixed-alpha minima."""
from collections import defaultdict
from functools import cache
from heapq import heappush, heappop
from itertools import combinations, combinations_with_replacement
from math import comb


def C(a, b):
    return comb(a, b) if 0 <= b <= a else 0


def ceiling(a, b):
    return -((-a) // b)


def tri_lb(n, e):
    return max(0, ceiling(4 * e * e - n * n * e, 3 * n)) if n else 0


def colored_caps(n, r):
    """Direct colex, checking all immediate subfaces of each admissible face."""
    faces = [[] for _ in range(r + 1)]
    for k in range(1, r + 1):
        for vertices in combinations(range(n), k):
            if len({v % r for v in vertices}) == k:
                faces[k].append(sum(1 << v for v in vertices))
        faces[k].sort()
    ans = {}
    for k in range(1, r):
        index = {mask: i for i, mask in enumerate(faces[k], 1)}
        counts = [0] * (len(index) + 1)
        for m in faces[k + 1]:
            bits = [1 << v for v in range(n) if m >> v & 1]
            limit = max(index[m ^ bit] for bit in bits)
            counts[limit] += 1
        for i in range(1, len(counts)):
            counts[i] += counts[i - 1]
        ans[k] = counts
    return ans


def lower_table(n, r):
    """Certified numerical lower envelopes for all feasible edge counts."""
    q = n - r
    values = {}
    for D in combinations_with_replacement(range(r), q):
        baseline = [C(r, j) + sum(C(d, j - 1) for d in D)
                    for j in range(3, r + 1)]
        pairwise = sorted(max(0, a + b - r) for a, b in combinations(D, 2))
        initial = C(r, 2) + sum(D)
        for e in range(len(pairwise) + 1):
            m = initial + e
            entry = baseline.copy()
            entry[0] = max(entry[0] + tri_lb(q, e), tri_lb(n, m))
            if m in values:
                values[m] = list(map(min, zip(values[m], entry)))
            else:
                values[m] = entry
            if e < len(pairwise):
                d = pairwise[e]
                for i in range(len(baseline)):
                    baseline[i] += C(d, i + 1)
    return values


def upper_sweep(segments):
    """For each attained integer next count, retain largest predecessor."""
    if not segments:
        return {}
    segments.sort()
    h = []
    i = 0
    answer = {}
    for v in range(segments[0][0], max(hi for lo, hi, a in segments) + 1):
        while i < len(segments) and segments[i][0] <= v:
            lo, hi, a = segments[i]
            heappush(h, (-a, hi))
            i += 1
        while h and h[0][1] < v:
            heappop(h)
        if h:
            answer[v] = -h[0][0]
    return answer


def envelope(n, r):
    caps, lows = colored_caps(n, r), lower_table(n, r)
    out = {}
    for m in range(C(r, 2), caps[1][n] + 1):
        layers = [{}, {}, {}]
        layers[int(m < n)][m] = n
        crossings = set()
        for k in range(2, r):
            pending = [[], [], []]
            for flag, layer in enumerate(layers):
                for a, b in layer.items():
                    low = max(lows[m][k - 2],
                              ceiling(k*k*a*a - n*a*b, (k*k-1)*b))
                    high = caps[k][a]
                    if low > high:
                        continue
                    if flag == 2:
                        pending[2].append((low, high, a))
                    elif flag == 0:
                        if low < a:
                            pending[1].append((low, min(high, a - 1), a))
                        if high >= a:
                            pending[0].append((max(a, low), high, a))
                    else:
                        if low <= a:
                            pending[1].append((low, min(a, high), a))
                        if high > a:
                            pending[2].append((max(low, a + 1), high, a))
                            crossings.add((k, a))
            layers = list(map(upper_sweep, pending))
        if layers[2]:
            out[m] = crossings
    return out


@cache
def ordinary_kk(number, k):
    """The ordinary binomial representation, with exact integer tests."""
    value = 0
    while number:
        a = k
        while C(a + 1, k) <= number:
            a += 1
        number -= C(a, k)
        value += C(a, k + 1)
        k -= 1
    return value


@cache
def alloc_profile(caps):
    """Exact greatest sum of choose(c_i,2) at each attainable sum."""
    profile = [0]
    for cap in caps:
        nxt = [-1] * (len(profile) + cap)
        for i, v in enumerate(profile):
            for c in range(cap + 1):
                nxt[i + c] = max(nxt[i + c], v + C(c, 2))
        profile = nxt
    return profile


def residual(n, r, target):
    q = n - r
    maxima = dict.fromkeys(target, -1)
    by_m = defaultdict(list)
    for m, t in target:
        by_m[m].append(t)
    m_min, m_max = min(by_m), max(by_m)
    for D in combinations_with_replacement(range(r), q):
        initial = C(r, 2) + sum(D)
        if initial > m_max or initial + C(q, 2) < m_min:
            continue
        baseline_3 = C(r, 3) + sum(C(d, 2) for d in D)
        baseline_4 = C(r, 4) + sum(C(d, 3) for d in D)
        ds = list(combinations(D, 2))
        low_list = sorted(max(0, a + b - r) for a, b in ds)
        cap_list = sorted((min(a, b, r - 2) for a, b in ds), reverse=True)
        for m, ts in by_m.items():
            e = m - initial
            if not 0 <= e <= C(q, 2):
                continue
            lo_t = tri_lb(q, e)
            hi_t = ordinary_kk(e, 2)
            lo_S = sum(low_list[:e])
            cap = tuple(cap_list[:e])
            for t in ts:
                for u in range(lo_t, min(hi_t, t - baseline_3 - lo_S) + 1):
                    S = t - baseline_3 - u
                    if S > sum(cap):
                        continue
                    two = alloc_profile(cap)[S]
                    three = min(ordinary_kk(S, 2), (q - 2) * S // 3,
                                u * min(r - 3, D[-3]))
                    four = min(ordinary_kk(u, 3), (q - 3) * u // 4)
                    maxima[m,t] = max(maxima[m,t], baseline_4 + two + three + four)
    return maxima


def clique_vector(n, edges, rank):
    return [sum(all(edge in edges for edge in combinations(vs, 2))
                for vs in combinations(range(n), k)) for k in range(rank + 1)]


def complete_parts(sizes):
    labels = [i for i, size in enumerate(sizes) for _ in range(size)]
    return {(i, j) for i, j in combinations(range(len(labels)), 2)
            if labels[i] != labels[j]}


def main():
    n = 15
    remaining = {}
    for r in range(3, n + 1):
        keep = envelope(n, r)
        if keep:
            remaining[r] = keep
        print('rank', r, 'edge counts', sorted(keep), flush=True)
    assert set(remaining) == {5,6,7,9}, remaining
    assert remaining[5] == {14:{(2,14)}}, remaining[5]
    assert set(remaining[9]) == set(range(70,83))
    assert all(k == 4 for xs in remaining[9].values() for k, a in xs)
    for r, count, margin in [(6, 12, -11), (7, 48, -2)]:
        target = {(m,a) for m, xs in remaining[r].items() for k,a in xs}
        assert all(k == 3 and a < m for m,xs in remaining[r].items() for k,a in xs)
        assert len(target) == count
        results = residual(n, r, target)
        gap = max(v - a for (m,a),v in results.items() if v >= 0)
        assert gap == margin, (gap, results)
        print('rank', r, 'four-clique deficit', gap, 'from', len(target), 'pairs', flush=True)
    for r, n_first, threshold in [(3, 33, 32), (4, 19, 18)]:
        caps = colored_caps(n_first, r)[2]
        assert min(m for m, t in enumerate(caps) if t > m) == threshold
    e15 = set(combinations(range(6), 2)) - {(0,1)}
    assert clique_vector(15, e15, 6) == [1,15,14,16,9,2,0]
    assert C(15,2) * C(13,4) == 75075
    assert clique_vector(33, complete_parts((4,3,3)) - {(0,4)}, 4) == [1,33,32,33,0]
    assert clique_vector(19, complete_parts((2,2,2,1)), 5) == [1,19,18,20,8,0]
    print('All exact checks passed.')


if __name__ == '__main__':
    main()
