#!/usr/bin/env python3
"""Literal keyword-union queries, exact matchings and all-shapes DP."""
from collections import Counter
from functools import lru_cache
from fractions import Fraction as F
from itertools import combinations, product
from random import Random


@lru_cache(None)
def matchings(g):
    if not g:
        return ((),)
    first, *rest = g
    return tuple(((first, v),) + tail
                 for i, v in enumerate(rest)
                 for tail in matchings(tuple(rest[:i] + rest[i+1:])))


def labels_by_subset(labels):
    out = [0] * (1 << len(labels))
    for s in range(1, len(out)):
        lsb = s & -s
        out[s] = out[s ^ lsb] | labels[lsb.bit_length()-1]
    return out


def tree_opt(cost):
    @lru_cache(None)
    def dp(s):
        if s.bit_count() == 1:
            return 0
        a, best = (s-1) & s, None
        while a:
            if a & (s & -s):  # the least set bit belongs to a
                v = dp(a) + dp(s ^ a)
                best = v if best is None else min(best, v)
            a = (a-1) & s
        return cost[s] + best
    return dp(len(cost)-1)


def lo_costs(cost):
    n = (len(cost)-1).bit_count()
    @lru_cache(None)
    def go(nodes):
        if len(nodes) == 1:
            return Counter({0: 1})
        all_next = [tuple(sorted(nodes[i] | nodes[j] for i, j in m))
                    for m in matchings(tuple(range(len(nodes))))]
        costs = [sum(cost[s] for s in p) for p in all_next]
        best = min(costs)
        out = Counter()
        for p, c in zip(all_next, costs):
            if c == best:
                for later, ways in go(p).items():
                    out[c+later] += ways
        return out
    return go(tuple(1 << i for i in range(n)))


def exact_family(n, combined=False, eta=None):
    m = n//2
    eta = F(1, n*n) if eta is None else eta
    labels = [1 << i for i in range(n)]
    main = []
    for col in range(1, (1 << m)-1):
        a, b = 1 << (n+2*len(main)), 1 << (n+2*len(main)+1)
        main.append(a | b)
        for i in range(m):
            if col >> i & 1:
                labels[m+i] |= b
            else:
                labels[i] |= a
    controls = [(1 << i) | (1 << j) for i, j in combinations(range(n),2)
                if not (i < m and j == m+i)]
    mask_labels = labels_by_subset(labels)
    costs = []
    for s in mask_labels:
        hits = sum(s & q == q for q in main)
        a = int(hits > 0) if combined else F(hits,len(main))
        b = F(sum(s & q == q for q in controls), len(controls))
        costs.append((1-eta)*a + eta*b)
    return costs


def first_minimizers(cost):
    n = (len(cost)-1).bit_count()
    result = [(sum(cost[(1<<i)|(1<<j)] for i,j in v), v)
              for v in matchings(tuple(range(n)))]
    best = min(c for c, _ in result)
    return best, [v for c,v in result if c == best]


def check_lower():
    for n in (4, 8):
        m, k = n//2, n.bit_length()-1
        for combined in (False, True):
            cost = exact_family(n,combined)
            b, ties = first_minimizers(cost)
            assert b == 0 and ties == [tuple((i,m+i) for i in range(m))]
            opt = tree_opt(cost)
            assert 1 <= opt <= 1-F(1,n*n)+F(k,n*n)
            all_lo = lo_costs(cost)
            a = (n//2-1 if combined else
                 sum(F(n,2**h) * (1-F(2,2**(2**(h-1))))/(1-F(2,2**m))
                     for h in range(1,k+1)))
            assert min(all_lo) >= (1-F(1,n*n))*a
            assert max(all_lo) <= F(n,2)*opt
            print(f'n={n} {"OR-of-pairs" if combined else "pair-AND"}: '
                  f'unique first layer, {sum(all_lo.values())} LO outputs, '
                  f'OPT={opt}, SLC range=[{min(all_lo)},{max(all_lo)}]')
        b, ties = first_minimizers(exact_family(n,False,F(0)))
        assert b == 0 and len(ties) > 1
    print('negative control: dropping private-marker mass loses uniqueness')


def split_costs(labels, ordinary, exceptional):
    unions = labels_by_subset(labels)
    n = len(labels)
    # 011/100 represent two shared tests, and the third-coordinate
    # disjunction component can vary independently across mixtures.
    prof = [(int(bool(s & 3)), int(bool(s & 4))) for s in unions]
    d = [sum(w for m,w in ordinary if s & m) for s in unions]
    x = [sum(w*tab[2*a+b] for tab,w in exceptional) for a,b in prof]
    cost = [a+b for a,b in zip(d,x)]
    D0 = sum(d[1 << i] for i in range(n))
    WX = x[-1]
    states = {tuple(1 << i for i in range(n))}
    transitions = 0
    while len(next(iter(states))) > 1:
        new = set()
        for nodes in states:
            current = sum(cost[s] for s in nodes)
            layer_d = sum(d[s] for s in nodes)
            assert layer_d <= D0
            firsts = [tuple(sorted(nodes[i] | nodes[j] for i,j in m))
                      for m in matchings(tuple(range(len(nodes))))]
            best = min(sum(cost[s] for s in p) for p in firsts)
            assert 2*best <= current + layer_d + 4*WX
            for p in firsts:
                if sum(cost[s] for s in p) == best:
                    assert sum(d[s] for s in p) <= layer_d
                    transitions += 1
                    new.add(p)
        states = new
    opt = tree_opt(cost)
    assert sum(cost[1<<i] for i in range(n)) <= 2*opt
    assert max(lo_costs(cost)) <= 6*(n.bit_length()-1)*opt
    return transitions


def check_positive():
    one = [(1, F(1,7)), (5,F(2,7))]
    ands = [((0,0,0,1),F(4,7))]
    rng = Random(20261127)
    a = sum(split_costs(s,one,ands) for s in product(range(8),repeat=4))
    b = sum(split_costs(tuple(rng.randrange(8) for _ in range(8)),
                        [(1,F(2,9)),(6,F(3,9))],
                        [((0,0,0,1),F(2,9)),((0,1,1,1),F(2,9))])
            for _ in range(32))
    print(f'fixed-summary positives: 4096 four-leaf and 32 eight-leaf instances; '
          f'{a+b} minimum-matching transitions checked exactly')


if __name__ == '__main__':
    check_lower()
    check_positive()
    print('PASS literal Boolean workload, all-shapes OPT, and all small minimum ties')
