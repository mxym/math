"""Reconstruct and refute a rank-38 two-type panel with common positive masks 15,19,21,22."""

import argparse
from collections import Counter
import gzip
from itertools import permutations, product
import json
from pathlib import Path

import pynauty

from enumerate_cores import gluings, mask, members, orders, supports
from exact_overlap import check_dual, check_integer, contact_columns
from forced_pair import acceptable

HERE = Path(__file__).resolve().parent


def wings(genbg, common_rows=(15,19,21,22)):
    p = len(common_rows)
    charts = set()
    for graph in supports(genbg):
        neighbors = [set(members(r)) for r in graph]
        sites = set(range(18))
        for root in sites:
            positives = set(range(9)) if root < 9 else set(range(9,18))
            for a,b,c,d in permutations(neighbors[root]):
                parents = (a,b,c,d)
                other = [set.intersection(*(neighbors[parents[j]] for j in members(row & 15)))-{root}
                         for row in common_rows[1:]]
                if not all(len(pair) == 1 for pair in other):
                    continue
                labels = [next(iter(pair)) for pair in other]
                if len(set(labels)) != p-1:
                    continue
                extra = (sites-positives)-neighbors[root]
                for more in permutations(sorted(extra), 5-p):
                    common = [root,*labels,*parents,*more]
                    panel = set(common)
                    if len(panel) != 9 or not acceptable(panel,neighbors) or not acceptable(sites-panel,neighbors):
                        continue
                    if any(sum(1<<j for j,y in enumerate(common[p:]) if y in neighbors[z]) != v
                           for z,v in zip(common[:p],common_rows)):
                        continue
                    _, left = orders((sites-panel)-positives,common,graph)
                    _, right = orders((sites-panel)&positives,common,graph)
                    _, l, r = min((tuple(mask(j for j,y in enumerate(rr) if y in neighbors[x]) for x in ll),ll,rr)
                                  for ll,rr in product(left,right))
                    order = common+list(l)+list(r)
                    charts.add(tuple(mask(j for j,y in enumerate(order) if y in neighbors[x]) for x in order))
    assert len(charts) == {
        (15,19,21,22):72, (15,51,60):88, (15,19,21,26):128,
        (15,3,21,22):318, (15,3,21,26):488, (15,3,21,28):370,
    }[common_rows]
    return list(map(list,sorted(charts)))


def canonical(graph, first_sign=4):
    colors = [sites for s in (0,9,18) for sites in
              (set(range(s,s+first_sign)),set(range(s+first_sign,s+9)))]
    return pynauty.certificate(pynauty.Graph(
        27, adjacency_dict={i:list(members(r)) for i,r in enumerate(graph)}, vertex_coloring=colors))


def contact_test(graph, first_sign=4):
    target, columns = contact_columns(graph,first_sign)
    first_upper = len(target)
    triples = []
    high = []
    # Support on the other two panels, one group of original positives in each.
    pos = (1 << first_sign)-1
    neg = 511 ^ pos
    positive = [(neg<<9)|(pos<<18), pos|(neg<<18), pos|(neg<<9)]
    for panel in range(3):
        group = 511 << (9*panel)
        height = {i:4-(graph[i]&group).bit_count() for i in members(group)}
        assert max(height.values()) <= 3
        triples.append(mask(i for i,h in height.items() if h == 3))
        high.append(mask(i for i,h in height.items() if h >= 2))
    capacity = [1-t.bit_count() for t in triples]
    assert min(capacity) >= 0
    filtered = []
    for sites,col in columns:
        w = mask(sites)
        h = [(w & side).bit_count() for side in positive]
        if any(v > 3 or (v >= 2 and w & triples[i]) or
               (v == 3 and (not capacity[i] or w & high[i])) for i,v in enumerate(h)):
            continue
        filtered.append((sites,col+[first_upper+i for i,v in enumerate(h) if v == 3]))
    return target+capacity, filtered, first_upper



def check_example():
    model = json.loads((HERE/'exterior-contact-example.json').read_text())
    graph, words = model['core'], model['contacts']
    p = model['p']
    assert p == 3 and len(graph) == 27 and len(words) == 72
    sign = [1 if i%9 < p else -1 for i in range(27)]
    for a,b in ((0,1),(0,2),(1,2)):
        t = [s if i//9 == a else -s if i//9 == b else 0 for i,s in enumerate(sign)]
        assert all(sum(t[j] for j in members(row)) == -4*t[i] for i,row in enumerate(graph))
        assert all(sum(t[j] for j in members(word)) == 0 for word in words)
    assert all((x & y).bit_count() <= 2 for i,x in enumerate(words) for y in words[:i])
    target,columns,first_upper = contact_test(graph,p)
    by_word = {mask(sites):col for sites,col in columns}
    counts = [0]*len(target)
    for word in words:
        for j in by_word[word]:
            counts[j] += 1
    assert counts[:first_upper] == target[:first_upper]
    assert all(a <= b for a,b in zip(counts[first_upper:],target[first_upper:]))

    # Exterior site 9 and core site 25 have no common neighbor yet.
    # An exterior edge needs at most one shared core contact and cannot
    # supply another common neighbor to a core site whose quota is full.
    assert Counter(w.bit_count() for w in words) == {0:4,2:6,3:30,4:30,6:2}
    x = words[9]
    missing = [2-((x>>j)&1)-(x & row).bit_count() for j,row in enumerate(graph)]
    candidates = [i for i,y in enumerate(words) if i != 9 and y & (1<<25)
                  and (x&y).bit_count() <= 1 and all(missing[j] for j in members(y))]
    assert missing[25] == 2 and candidates == [56]
    print('Exterior contact example: one available common neighbor where two are required.')

def three_positive_cores(genbg):
    representatives = {}
    for g in gluings(wings(genbg,(15,51,60)),3):
        representatives.setdefault(canonical(g,3),g)
    assert len(representatives) == 99
    return representatives.values()


def six_contacts(genbg):
    for graph in three_positive_cores(genbg):
        target,cols,_ = contact_test(graph,3)
        assert {len(sites) for sites,col in cols} == {0,2,3,4,6}
        assert sum(target[28:379]) == 306
    allowed = []
    for k in range(7):
        z = 6-k
        if z*(z-1) >= 12*z-(36-3*k)-6*k:
            allowed.append(k)
    assert allowed == [2,3,4,5,6]
    print('All 99 cores have contact sizes 0,2,3,4,6 and require at least two six-contact sites.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--genbg', default='genbg')
    parser.add_argument('--drat-trim',required=True)
    args = parser.parse_args()
    with gzip.open(HERE/'conditional-panel.json.gz','rt') as file:
        cases = json.load(file)
    graph_set = {canonical(g) for g in gluings(wings(args.genbg),4)}
    assert len(cases) == len(graph_set) == 2592
    assert graph_set == {canonical(graph) for graph,certificate in cases}
    stats = Counter()
    for graph, dual in cases:
        target,columns,first_upper = contact_test(graph)
        if dual is None:
            check_integer(target,columns,args.drat_trim,upper_start=first_upper,limit_sites=True)
            stats['DRAT'] += 1
        else:
            assert all(i < first_upper or v >= 0 for i,v in dual)
            check_dual(target,columns,dual)
            stats['integer inequalities'] += 1
    assert stats == {'integer inequalities':2404,'DRAT':188}
    print(dict(stats))
    check_example()
    six_contacts(args.genbg)


if __name__ == '__main__':
    main()
