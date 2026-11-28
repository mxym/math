#!/usr/bin/env python3
"""Independent finite relation-table checks on a fixed prime toy. No inputs."""
from itertools import product
from functools import cache

SUPPORT = (5, 11, 23, 47)
A = lambda x, y: (y-2*x-1)*(y-3*x+4) == 0
B = lambda x, y: (y-2*x-1)*(y-x-6) == 0
C = lambda x, y: (3*y-4*x-25)*(y-4*x+21) == 0
D = lambda x, y: y-4*x-3 == 0
F = lambda x, y: y-2*x-1 == 0
rels = (A, B, C, D, F)
network = ("and", ("series", ("and", 0, 1), 2), 3)
witnesses = {(x, u, y) for x, u, y in product(SUPPORT, repeat=3)
             if x != u and u != y and x != y and A(x,u) and B(x,u)
             and C(u,y) and D(x,y)}
assert witnesses == {(5, 11, 23)}

@cache
def sinks(gate, source):
    if isinstance(gate, int):
        return frozenset(p for p in SUPPORT
                         if p != source and rels[gate](source, p))
    op, left, right = gate
    if op == "and":
        return sinks(left, source) & sinks(right, source)
    return frozenset(q for u in sinks(left, source) for q in sinks(right, u))

genuine = {(p,q) for p in SUPPORT for q in sinks(network,p)}
assert genuine == {(p,q) for p,u,q in witnesses}
edges = {tuple(sorted((p,q))) for p,q in product(SUPPORT, repeat=2)
         if p != q and any(f(p,q) or f(q,p) for f in rels)}
assert (23,47) in edges
visited = {5}
for _ in SUPPORT:
    visited |= {q for p,q in edges if p in visited} | {p for p,q in edges if q in visited}
assert visited == set(SUPPORT)
assert 47 not in {p for v in witnesses for p in v}

# Test the memoized recurrence independently against explicit membership
# for every small binary AND/series arrangement with up to three leaves.
leaves = (0, 1, 2, 3, 4)
tests = 0
trees = list(leaves)
pairs = [(op,i,j) for op in ("and","series") for i,j in product(leaves,repeat=2)]
trees += pairs
trees += [(op,i,j) for op in ("and","series") for i,j in product(pairs,leaves)]
trees += [(op,i,j) for op in ("and","series") for i,j in product(leaves,pairs)]

def fresh(g):
    # Flatten each formula to explicitly shared vertex ids.
    nxt = 2
    edges = []
    def visit(node, a, b):
        nonlocal nxt
        if isinstance(node, int):
            edges.append((a,b,node))
            return
        op, left, right = node
        if op == "and":
            visit(left,a,b)
            visit(right,a,b)
        else:
            c = nxt
            nxt += 1
            visit(left,a,c)
            visit(right,c,b)
    visit(g,0,1)
    return nxt, edges

for g in trees:
    n, edges = fresh(g)
    explicit = {(v[0],v[1]) for v in product(SUPPORT,repeat=n)
                if all(v[a] != v[b] and rels[f](v[a],v[b])
                       for a,b,f in edges)}
    assert explicit == {(p,q) for p in SUPPORT for q in sinks(g,p)}
    tests += 1
assert tests == 1055
print("PASS: unique shared prime witness, connected extension, and 1055 exhaustive formula comparisons")
