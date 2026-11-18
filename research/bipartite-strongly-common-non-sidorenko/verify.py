#!/usr/bin/env python3
"""Finite scope only: incidence table, selected square, threshold arithmetic."""
from collections import Counter
from itertools import combinations

FACES = [
    (0,1,3),(0,1,9),(0,2,3),(0,2,9),(1,3,10),(1,7,10),(1,7,12),
    (1,9,12),(2,3,4),(2,4,9),(3,4,11),(3,10,11),(4,8,9),(4,8,11),
    (5,6,7),(5,6,11),(5,7,10),(5,10,11),(6,7,12),(6,8,11),
    (6,8,12),(8,9,12),
]

def check(ok, message):
    if not ok:
        raise ValueError(message)

points = set().union(*map(set, FACES))
a, b = len(points), len(FACES)
edges = {(i,j) for j,f in enumerate(FACES) for i in f}
e = len(edges)
check((a,b,e)==(13,22,66) and a+b==35, "graph parameters")
check(points==set(range(13)) and len(set(FACES))==22, "point/face labels")
check(all(tuple(sorted(set(f)))==f and len(f)==3 for f in FACES), "simple triples")
matches = Counter(pair for f in FACES for pair in combinations(f,2))
check(len(matches)==33 and set(matches.values())=={2}, "two faces per used pair")
check([j for j,f in enumerate(FACES) if {0,1}<=set(f)]==[0,1], "chosen square")
frontier={('p',0)}; seen=set()
while frontier:
    seen.update(frontier)
    nxt=set()
    for side,idx in frontier:
        if side=='p': nxt.update(('f',j) for i,j in edges if i==idx)
        else: nxt.update(('p',i) for i,j in edges if j==idx)
    frontier=nxt-seen
check(len(seen)==a+b, "connected incidence graph (the padded graph is not connected)")
M=2**650
check(18*2**(e+a*b)<2**357<M, "strong two-color threshold")
check((1+2*4**2)*2**e*4**(a*b)==33*2**638<2**644<M, "two-color density threshold")
# For q=3/4 the sparse color bound follows from (3/4)^286 >= 2^-286
# and (3/2)^4 >= 2. Avoid raising a rational to the enormous exponent M.
check(3*2>=4 and 3**4>=2*2**4 and M-a*b>=1-e, "sparse two-color bound")
print("H: 13 points, 22 faces, 66 incidences; chosen square and thresholds verified.")
