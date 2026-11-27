#!/usr/bin/env python3
"""Verify finite derivative laws and exact rank/failure parameters."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from random import Random


def rank(seq):
    rows = {}
    for v in seq:
        while v:
            bit = v.bit_length() - 1
            if bit not in rows:
                rows[bit] = v
                break
            v ^= rows[bit]
    return len(rows)


def xor(seq):
    x = 0
    for y in seq:
        x ^= y
    return x


def delta(table, directions):
    for a in directions:
        table = tuple(value ^ table[x ^ a] for x, value in enumerate(table))
    return table


def anf_degree(table):
    n = len(table).bit_length() - 1
    basis = list(table)
    for j in range(n):
        for i in range(1 << n):
            if i >> j & 1:
                basis[i] ^= basis[i ^ (1 << j)]
    return max((i.bit_count() for i,v in enumerate(basis) if v), default=0)


def make_map(n, d, g):
    coeffs = [(i, g.randrange(32)) for i in range(1 << n) if i.bit_count() <= d]
    return tuple(xor(y for i,y in coeffs if (x & i) == i) for x in range(1 << n))


g = Random(261107266)
ind_tests = dep_tests = 0
for d in range(2, 6):
    n = d + 1
    table = make_map(n,d,g)
    assert anf_degree(table) <= d
    for _ in range(600):
        a = tuple(g.randrange(1 << n) for _ in range(d-1))
        der = delta(table, a)
        if rank(a) < d-1:
            assert der == (0,) * (1 << n)
            dep_tests += 1
        else:
            dist = Counter(der)
            assert len(set(dist.values())) == 1
            cols = [delta(table, a + (1 << j,))[0] for j in range(n)]
            assert len(dist) == 1 << rank(cols)
            for c in (0, 1, 3, (1 << n)-1):
                assert len(set(delta(table,a+(c,)))) == 1
            ind_tests += 1
    if d >= 4:
        assert not any(delta(table,(1,2,3)+(8,)*(d-4)))
assert delta((0,0,0,1), (1,2)) == (1,1,1,1)  # nonzero independent negative control
print(f"finite derivative laws: {ind_tests} independent, {dep_tests} dependent PASS")

ind = 0
for n, p in ((1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)):
    count = sum(rank(a) == p for a in product(range(1 << n),repeat=p))
    expected = 1
    for j in range(p):
        expected *= (1 << n)-(1 << j)
    assert count == expected
    ind += count
print(f"ordered independent tuple count: {ind} tuples across seven models PASS")


def include(row, r, steps):
    law = {0:F(1)}
    for _ in range(steps):
        nxt = Counter()
        for q, prob in law.items():
            stay = F(1 << q, 1 << r)
            nxt[q] += prob*stay
            nxt[q+1] += prob*(1-stay)
        law = nxt
    return sum(law.get(i,F(0)) for i in range(row))


exact = general = 0
for d in range(2, 13):
    p = d-1
    for m in (8*d,8*d+1,8*d+3,12*d):
        r = m//2
        e = (m-r+1)*(m-p-r+1)
        assert 16*e >= 3*m*m and e >= (p+2)*m
        union = F(comb(m-p,r-1), 1 << e)
        assert (1 << (p*m))*union <= F(1, 1 << (m+p))
        assert F(1,16)+F(1,8)+(1 << (p*m))*union < 1
        if d <= 6:
            assert include(r, m, m-p) <= union
            exact += 1
        # Worst-case dimension (for an existential random choice);
        # using exponent arithmetic rather than floating point.
        out = m//2-1
        m_choose_d = comb(m,d)
        s0 = out*m_choose_d//(2*m)
        assert 3*out >= m and s0 >= m and 2*m*s0 <= out*m_choose_d
        general += 1
print(f"sparse-branch constants and sharpness counts: {general} sets, {exact} exact rank laws PASS")
