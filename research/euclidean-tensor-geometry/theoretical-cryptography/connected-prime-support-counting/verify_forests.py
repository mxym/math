"""Fixed, exhaustive small graph check of the multi-root Catalan bound."""
from itertools import combinations
from math import comb

n = 5
pairs = list(combinations(range(n), 2))
full = (1<<n)-1
cells = witnessed = 0
for code in range(1<<len(pairs)):
    adj = [0]*n
    for i, (v,w) in enumerate(pairs):
        if code>>i & 1:
            adj[v] |= 1<<w
            adj[w] |= 1<<v
    delta = max(x.bit_count() for x in adj)
    for roots in range(1, full+1):
        t = roots.bit_count()
        counts = [0]*(n-t+1)
        extra = full ^ roots
        add = extra
        while True:
            support = roots | add
            reached = roots
            while True:
                grow = reached
                for v in range(n):
                    if reached>>v & 1:
                        grow |= adj[v] & support
                if grow == reached: break
                reached = grow
            if reached == support:
                counts[add.bit_count()] += 1
                witnessed += 1
            if not add: break
            add = (add-1)&extra
        for j,num in enumerate(counts):
            shapes = t * comb(2*j+t,j) // (2*j+t)
            assert num <= shapes * delta**j
            cells += 1
print("PASS: graphs",1<<len(pairs),"multi-root coefficients",cells,
      "covered labeled root/support pairs",witnessed)
