#!/usr/bin/env python3
"""Four-type matching count, exact finite-field powering, and series."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
from math import comb


def recursive_pairs(positions):
    if not positions:
        yield ()
    else:
        for j in range(1,len(positions)):
            for tail in recursive_pairs(positions[1:j]+positions[j+1:]):
                yield ((positions[0],positions[j]),)+tail


def check_random_round():
    types_count = 0
    for g in (2,4,6,8):
        perfect = tuple(recursive_pairs(tuple(range(g))))
        assert all(len(x)==g//2 for x in perfect)
        for c in range(g+1):
            for a in range(g-c+1):
                for b in range(g-c-a+1):
                    nodes = [3]*c + [1]*a + [2]*b + [0]*(g-c-a-b)
                    numerator = sum(sum((nodes[i] | nodes[j]) == 3 for i,j in x)
                                    for x in perfect)
                    expected = Q(numerator,len(perfect))
                    assert expected == Q(c*(g-c)+comb(c,2)+a*b,g-1)
                    x = Q(c,g)
                    f = 1-(1-x)**2/2
                    assert expected/(g//2) <= f+Q(1,g-1)
                    types_count += 1
    print(f'independent random-matching profile count: {types_count} exact compositions')


def multiply(a,b,mod):
    d = mod.bit_length()-1
    prod = 0
    for i in range(d):
        if b >> i & 1:
            prod ^= a << i
    for i in range(2*d-2,d-1,-1):
        if prod >> i & 1:
            prod ^= mod << (i-d)
    return prod


def field_columns(m,mod):
    d = mod.bit_length()-1
    q = 1 << d
    assert q == m*m
    def mul(a,b):
        return multiply(a,b,mod)
    for a in range(1,q):
        assert {mul(a,b) for b in range(q)} == set(range(q))
    traces = []
    for a in range(q):
        acc = 0
        for _ in range(d):
            acc ^= a
            a = mul(a,a)
        assert acc in (0,1)
        traces.append(acc)
    assert sum(traces) == q//2
    columns = Counter()
    for v in range(q):
        p = [1]
        for _ in range(m-1):
            p.append(mul(p[-1],v))
        for u in range(q):
            col = sum(traces[mul(u,p[i])] << i for i in range(m))
            columns[col] += 1
    return q,columns


def check_powering():
    masks,groups = 0,0
    for m,mod in ((2,0x7),(4,0x13),(8,0x43)):
        q,cols = field_columns(m,mod)
        assert sum(cols.values()) == q*q
        const = cols[0]+cols[(1<<m)-1]
        assert const < q*q
        for mask in range(1,1<<m):
            bias = Q(sum((-1)**((col&mask).bit_count()%2)*w for col,w in cols.items()), q*q)
            assert 0 <= bias <= Q(m-1,q) < Q(1,m)
            masks += 1
            k = mask.bit_count()
            equal = sum(w for col,w in cols.items() if (col & mask) in (0,mask))
            acceptance = 1-Q(equal,q*q)
            exact = 1-Q(2,2**k)
            assert abs(acceptance-exact) < Q(1,m)
            assert Q(q*q-equal,q*q-const) >= acceptance
            if k == 2:
                assert equal < q*q
            groups += 1
        print(f'powering m={m}: {q*q} columns, {q*q-const} nonconstant, '
              f'all {(1<<m)-1} masks/groups pass')
    # Independently verify the closed all-equal indicator by its parity characters.
    for k in range(1,7):
        for bits in range(1<<k):
            total = sum((-1)**((bits&s).bit_count()%2) for s in range(1<<k)
                        if not s.bit_count()%2)
            assert total == (2**(k-1) if bits in (0,(1<<k)-1) else 0)
    print(f'independent field totals: {masks} parity bounds, {groups} all-equal bounds; '
          'indicator checked exhaustively at sizes 1..6')


def check_series_and_visits():
    z = Q(0)
    subtotal = Q(0)
    for h in range(1,9):
        assert z == 1-Q(1,2**(2**(h-1)-1))
        subtotal += z/2**h
        z = 1-(1-z)**2/2
    hi = subtotal+Q(1,2**8)
    lo = hi-(1-z)/2**8
    assert Q(358885765068,10**12) < lo <= hi < Q(358885765069,10**12)
    # Balanced and unbalanced trees, two tags and all six monotone
    # two-bit truth tables, directly comparing traversal and SLC.
    shapes = (((0,1),(2,3)),(0,((1,2),3)))
    queries = ((0,0,0,0),(0,0,0,1),(0,0,1,1),(0,1,0,1),(0,1,1,1),(1,1,1,1))
    def child_labels(tree,x):
        if isinstance(tree,int):
            return x[tree],()
        a,b = (child_labels(t,x) for t in tree)
        return a[0] | b[0],(a,b)
    def scan(node,test):
        return 1+(sum(scan(c,test) for c in node[1]) if test[node[0]] else 0)
    def count(node,test):
        return (test[node[0]]+sum(count(c,test) for c in node[1])) if node[1] else 0
    checked = 0
    for x in range(4**4):
        tags = [(x >> (2*i)) & 3 for i in range(4)]
        for shape in shapes:
            node = child_labels(shape,tags)
            for t in queries:
                assert scan(node,t) == 1+2*count(node,t)
                checked += 1
    print(f'sharp pair coefficient in (0.358885765068,0.358885765069); '
          f'{checked} direct root-inclusive traversal cases')
    print('PASS independent matching/finite-field/series/visit audit')


if __name__ == '__main__':
    check_random_round()
    check_powering()
    check_series_and_visits()
