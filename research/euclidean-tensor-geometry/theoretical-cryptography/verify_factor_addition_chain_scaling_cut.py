#!/usr/bin/env python3
"""Check the scaling-cut lemma on exhaustive small and seeded larger chains."""

from collections import Counter, deque
from itertools import combinations_with_replacement
from random import Random


def require(condition, why):
    if not condition:
        raise AssertionError(why)


def witness(values, parent, star):
    last = len(values)-1
    use = {last}
    todo = [last]
    while todo:
        i = todo.pop()
        if i:
            for a in parent[i]:
                if a not in use:
                    use.add(a)
                    todo.append(a)
    require(0 in use, 'initial ancestor')
    # Single predecessor for standard doubling; two operands otherwise.
    cut_edges = [[] for _ in values]
    non = 0
    for i in sorted(use-{0}):
        a,b = parent[i]
        if a == b == i-1:
            cut_edges[a].append((i,1))
            cut_edges[i].append((a,0))
        else:
            non += 1
            for u in {a,b}:
                cut_edges[i].append((u,0))
                cut_edges[u].append((i,0))
    # Exact binary-exponent multiset, using counts rather than repeated leaves.
    counts = {0:Counter({0:1})}
    for i in sorted(use-{0}):
        a,b = parent[i]
        if a == b == i-1:
            counts[i] = Counter({k+1:v for k,v in counts[a].items()})
        else:
            counts[i] = counts[a]+counts[b]
        require(sum((1 << k)*v for k,v in counts[i].items()) == values[i],
                'unfolded target')
    j = (values[-1] & -values[-1]).bit_length()-1
    n = values[-1] >> j
    v = bin(n).count('1')
    lam = n.bit_length()-1
    q = sum(counts[last].values())
    require(v <= q <= 1 << non, 'raw leaf number')
    c = q-v
    require(min(counts[last]) >= j-c, 'minimum raw exponent')
    for t in counts.values():
        require(max(t)-min(t) <= lam+c, 'spread inheritance')

    infinity = len(values)+1
    dist = [infinity]*len(values)
    dist[0] = 0
    todo = deque([0])
    while todo:
        i = todo.popleft()
        for p,w in cut_edges[i]:
            if dist[i]+w < dist[p]:
                dist[p] = dist[i]+w
                if w:
                    todo.append(p)
                else:
                    todo.appendleft(p)
    # Independent Bellman-Ford for bounded sizes.
    if len(values) <= 11:
        dd = [0]+[infinity]*(len(values)-1)
        for _ in range(len(values)):
            old = dd.copy()
            for i,arcs in enumerate(cut_edges):
                for p,w in arcs:
                    dd[p] = min(dd[p],old[i]+w)
        require(dd == dist, 'independent shortest paths')
    require(dist[last] <= j, 'integral endpoint restriction')
    R = max(counts[last])-min(counts[last])
    require(dist[last] >= min(counts[last])-non*R, 'shortest cut spread bound')
    bound = non*lam+(non+1)*c
    require(dist[last] >= j-bound, 'dyadic cut bound')

    scaled = {}
    collapses = 0
    for i in sorted(use):
        h = min(dist[i], dist[last])
        require(not (values[i] % (1 << h)), 'integral scaled nodes')
        scaled[i] = values[i] >> h
        if i:
            a,b = parent[i]
            if (scaled[i],a,b)==(scaled[a],i-1,i-1):
                collapses += 1
            else:
                require(scaled[i] == scaled[a]+scaled[b], 'every noncollapsed sum')
    require(collapses >= dist[last] and
            scaled[last] << dist[last] == values[last], 'proper shortening')
    keep = sorted(set(scaled.values()))
    require(keep[0] == 1 and keep[-1] == (values[-1] >> dist[last]), 'canonical endpoints')
    for t in keep[1:]:
        require(any(scaled[a]+scaled[b] == t and scaled[a] < t and scaled[b] < t
                    for i in sorted(use-{0}) if scaled[i] == t for a,b in [parent[i]]),
                'ordinary canonical chain')
    if star:
        require(use == set(range(len(values))), 'star chain uses all')
        for i in range(1,len(values)):
            if scaled[i] != scaled[i-1]:
                require(i-1 in parent[i], 'scaled star parent')
                require(scaled[i] > scaled[i-1], 'scaled star increasing')
    return 'positive cut' if dist[last] else 'no cut', j > bound


def exhaustive(n, star):
    values = [1]
    parents = [None]
    stat = Counter()
    def work():
        if len(values) > 1:
            stat[witness(values,parents,star)] += 1
        if len(values) == n+1:
            return
        l = len(values)
        opts = ((a,l-1) for a in range(l)) if star else combinations_with_replacement(range(l),2)
        for a,b in opts:
            x = values[a]+values[b]
            if x <= values[-1]:
                continue
            values.append(x)
            parents.append((a,b))
            work()
            values.pop()
            parents.pop()
    work()
    return stat


def enlarge_bits(seq, pa, j):
    # Build the same computation after scaling every noninitial value by 2**j,
    # with initial doublings so that the old 1 is available at index j.
    new = [1 << k for k in range(j+1)] + [z << j for z in seq[1:]]
    pp = [None] + [(k-1,k-1) for k in range(1,j+1)] + [(a+j,b+j) for a,b in pa[1:]]
    return new,pp


def random_checks(number):
    r = Random(22371)
    stat = Counter()
    for it in range(number):
        star = bool(it%2)
        seq = [1]
        pa = [None]
        p = r.choice((.60,.75,.90))
        for k in range(1,r.randrange(5,45)):
            if r.random() < p:
                a=b=k-1
            else:
                a,b=sorted((r.randrange(k),r.randrange(k) if not star else k-1))
                if seq[a]+seq[b] <= seq[-1]:
                    b=k-1
            seq.append(seq[a]+seq[b])
            pa.append((a,b))
        stat[witness(seq,pa,star)] += 1
        scaled,pp=enlarge_bits(seq,pa,17+(it%83))
        stat[witness(scaled,pp,star)] += 1
    return stat


if __name__ == '__main__':
    for star in (False,True):
        ans = exhaustive(7,star)
        print('exhaustive',star,sum(ans.values()),sorted(ans.items()))
    ans = random_checks(3000)
    print('random plus directed large shifts',sum(ans.values()),sorted(ans.items()))
