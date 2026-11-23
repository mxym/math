"""Check all placements of a six-contact site for the (15,51,60) common panel."""

import argparse
from collections import Counter
from itertools import combinations

import pynauty

from enumerate_cores import mask, members
from exact_overlap import check_integer
from one_panel import contact_test, three_positive_cores


def extend(graph, word):
    n = len(graph)
    return tuple(row | (((word >> i) & 1) << n) for i,row in enumerate(graph)) + (word,)


def rooted_cases(cores):
    cases = {}
    first = {0,1,2,9,10,11,18,19,20}
    colors = [first,set(range(27))-first,{27}]
    for graph in cores:
        _, columns, _ = contact_test(graph,3)
        words = tuple(sorted(mask(sites) for sites,_ in columns))
        for sites,_ in columns:
            if len(sites) != 6:
                continue
            full = extend(graph,mask(sites))
            key = pynauty.certificate(pynauty.Graph(
                28, adjacency_dict={i:list(members(row)) for i,row in enumerate(full)}, vertex_coloring=colors))
            cases.setdefault(key,(full,words))
    assert len(cases) == 1128
    return [cases[k] for k in sorted(cases)]


def exterior_system(graph, previous_words):
    n = len(graph)
    pairs = list(combinations(range(n),2))
    pair_row = {pair:1+n+i for i,pair in enumerate(pairs)}
    target = [99-n] + [14-row.bit_count() for row in graph]
    target += [2-((graph[i] >> j)&1)-(graph[i]&graph[j]).bit_count() for i,j in pairs]
    assert min(target) >= 0
    closed = [row | (1 << i) for i,row in enumerate(graph)]
    columns = []
    for previous in previous_words:
        for word in (previous,previous | (1 << (n-1))):
            if any((word & r).bit_count() > 2 for r in closed):
                continue
            sites = tuple(members(word))
            col = [0] + [1+i for i in sites] + [pair_row[p] for p in combinations(sites,2)]
            if all(target[i] for i in col):
                columns.append((sites,col))
    return target, columns


def refute(graph, previous_words, drat_trim):
    target,columns = exterior_system(graph,previous_words)
    by_row = [[] for _ in target]
    words = []
    for sites,col in columns:
        w = mask(sites)
        words.append(w)
        for i in col:
            by_row[i].append(w)
    pending = [i for i in range(1,len(target)) if target[i]]
    if not pending:
        # A smaller closed component cannot occur since every nonneighbor
        # across the cut would have to have two common neighbors.
        if len(graph) < 99:
            return Counter(closed_component=1)
        raise AssertionError('a full 99-vertex completion survived')
    row = min(pending, key=lambda i:(len(by_row[i]),-target[i],-i))
    if not by_row[row]:
        return Counter(missing_quota=1)
    if not check_integer(target, columns, drat_trim, limit_sites=True, allow_sat=True):
        return Counter(DRAT=1)
    # Every completion supplies at least one of these exterior sites. The
    # fact that different branches may describe the same graph is harmless.
    counts = Counter(branch=1)
    for w in by_row[row]:
        counts.update(refute(extend(graph,w),words,drat_trim))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--genbg',default='genbg')
    parser.add_argument('--drat-trim',required=True)
    args = parser.parse_args()
    cases = rooted_cases(three_positive_cores(args.genbg))
    total = Counter()
    for graph,words in cases:
        total.update(refute(graph,words,args.drat_trim))
    print('Six-contact placements:',len(cases),'search nodes:',dict(total))


if __name__ == '__main__':
    main()
