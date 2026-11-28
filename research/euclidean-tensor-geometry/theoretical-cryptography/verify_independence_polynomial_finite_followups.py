#!/usr/bin/env python3
"""Exact certificate for order-16 rank five and the rank-nine 18/19 bracket."""
from itertools import combinations, combinations_with_replacement
from math import comb


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def ceildiv(x, y):
    return -((-x) // y)


def triangle_lower(n, e):
    return max(0, ceildiv(4*e*e - n*n*e, 3*n))


def colored_upper(n, r):
    faces = [[] for _ in range(r+1)]
    for mask in range(1, 1 << n):
        active = [i % r for i in range(n) if (mask >> i) & 1]
        if len(active) == len(set(active)):
            faces[len(active)].append(mask)
    upper = [None]
    for k in range(1, r):
        indices = {s: i for i, s in enumerate(faces[k], 1)}
        a = [0] * (len(faces[k])+1)
        for t in faces[k+1]:
            a[indices[t ^ (t & -t)]] += 1
        for i in range(1, len(a)):
            a[i] += a[i-1]
        upper.append(a)
    return upper


def fixed_clique_lower(n, r, max_edges):
    b = [None] * (max_edges+1)
    q = n-r
    pairs = tuple(combinations(range(q), 2))
    triangle = [triangle_lower(q, e) for e in range(len(pairs)+1)]
    full_triangle = [triangle_lower(n, e) for e in range(max_edges+1)]
    cc = [[choose(i, k) for k in range(r+1)] for i in range(r+1)]
    for ds in combinations_with_replacement(range(r), q):
        start = cc[r][2]+sum(ds)
        row = [cc[r][j]+sum(cc[d][j-1] for d in ds) for j in range(3, r+1)]
        ints = sorted(max(0, ds[i]+ds[j]-r) for i,j in pairs)
        for e in range(min(len(pairs), max_edges-start)+1):
            m = start+e
            lower = row.copy()
            lower[0] = max(lower[0]+triangle[e], full_triangle[m])
            if b[m] is None:
                b[m] = lower
            else:
                b[m] = [min(x,y) for x,y in zip(b[m],lower)]
            if e < len(ints):
                f = cc[ints[e]]
                row = [x+f[j] for j,x in enumerate(row,1)]
    return b


def possible(n, r):
    upper = colored_upper(n, r)
    b = fixed_clique_lower(n, r, upper[1][n])
    surviving = {}
    for m in range(choose(r,2), upper[1][n]+1):
        states = {(m, int(m<n)):n}
        crossings = set()
        for k in range(2, r):
            nxt = {}
            for (y,flag), x in states.items():
                mm = ceildiv(k*k*y*y - n*y*x, (k*k-1)*x)
                for z in range(max(1, b[m][k-2], mm), upper[k][y]+1):
                    if flag == 2 or flag == 1 and z>y:
                        end = 2
                    elif flag == 1 or z<y:
                        end = 1
                    else:
                        end = 0
                    if flag == 1 and end == 2:
                        crossings.add((k,y))
                    key = (z,end)
                    if x0 := nxt.get(key, 0):
                        if y > x0:
                            nxt[key] = y
                    else:
                        nxt[key] = y
            states = nxt
        if any(flag == 2 for y,flag in states):
            surviving[m] = crossings
    return surviving


def partitions(n, low=1):
    if n == 0:
        yield ()
    else:
        for a in range(low,n+1):
            for tail in partitions(n-a,a):
                yield (a,) + tail


def counts_mp(sizes):
    result = [1,0,0,0,0,0]
    for a in sizes:
        for i in range(5,0,-1):
            result[i] += a*result[i-1]
    return result


def count_check(n, edges, target):
    adj = [0]*n
    for a,b in edges:
        adj[a] |= 1<<b
        adj[b] |= 1<<a
    f = [0]*(n+1)
    def expand(S,k):
        f[k] += 1
        while S:
            u = S & -S
            S ^= u
            expand(S & adj[u.bit_length()-1], k+1)
    all_mask = (1<<n)-1
    expand(all_mask,0)
    while f[-1] == 0:
        f.pop()
    assert f == target, (f, target)
    todo = seen = 1
    while todo:
        x = todo & -todo
        todo ^= x
        reached = all_mask & ~(adj[x.bit_length()-1] | seen)
        seen |= reached
        todo |= reached
    assert seen == all_mask


def main():
    v16 = possible(16,5)
    assert v16 == {14:{(2,14)},15:{(2,15)}}
    for n in (17,18):
        row = possible(n,9)
        crossings = set().union(*row.values())
        assert crossings and min(x for k,x in crossings) == 175
        assert {k for k,x in crossings} == {4}
        print(n, len(row), min(row), max(row), len(crossings))
    pp = list(partitions(8))
    assert len(pp) == 22
    f = [counts_mp(p) for p in pp]
    a = [u[2]+u[3]-u[4] for u in f]
    assert max(a) == 40 and max(3*s+u[5] for s,u in zip(a,f)) == 120
    for d in range(7):
        assert choose(d,4) <= 1+3*(2-choose(d,2)+choose(d,3))
        assert choose(d,3) <= 3*(1-d+choose(d,2))
    for d in range(5):
        assert 2*choose(d,2) <= 3*d
    assert 126+8+120-3*27 == 173
    core = set(combinations(range(6),2)) - {(0,1)}
    add = (set(), {(6,7)}, {(0,6)}, {(2,6)})
    for extra in add:
        count_check(16, core | extra, [1,16,14+len(extra),16,9,2])
    labeled_core = choose(16,6)*choose(6,2)
    labeled = [labeled_core*x for x in (1,45,20,40)]
    assert labeled == [120120,5405400,2402400,4804800] and sum(labeled) == 12732720
    core = set(combinations(range(10),2)) - {(0,1)}
    groups = [range(10,13),range(13,16),range(16,19)]
    anchors = [(2,3,5),(3,4,6),(2,4,7)]
    for i, P in enumerate(groups):
        core.update((u,v) for u in anchors[i] for v in P)
        core.update((u,v) for Q in groups[i+1:] for u in P for v in Q)
    count_check(19, core, [1,19,98,193,191,196,140,64,17,2])
    print("PASS rank-nine bracket and rank-five classification")


if __name__ == "__main__":
    main()
