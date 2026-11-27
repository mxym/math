#!/usr/bin/env python3
"""Finite ratio-intersection certificate, entirely in integer bit sets."""
from itertools import permutations

P = 23
SIGMA = (22,6,13,2,9,5,16,10,1,20,14,4,18,3,19,21,12,17,8,7,11,15,0)
D = {i*i % P for i in range(1, P)}
assert D == {1,2,3,4,6,8,9,12,13,16,18}
assert len(set(SIGMA)) == P and set(SIGMA) == set(range(P))

def mask(items):
    return sum(1 << x for x in items)

def masks(order):
    return tuple(mask(i for i,k in enumerate(order) if (k-a) % P in D)
                 for a in range(P))

def signed_differences(cols):
    out = {}
    for a,c in permutations(range(P), 2):
        x,y = cols[a],cols[c]
        code = x & ~y, y & ~x
        assert code[0].bit_count() == code[1].bit_count() == 6
        assert code not in out
        out[code] = a,c
    return out

A = masks(range(P))
B = masks(SIGMA)
assert {((a & c).bit_count()) for a,c in permutations(A,2)} == {5}
F, G = signed_differences(A), signed_differences(B)
assert len(F) == len(G) == 506
M = sorted((F[key], G[key]) for key in F.keys() & G.keys())
assert M == [((0,1),(0,1)), ((1,0),(1,0))]
print(f'bit certificates: ordered differences {len(F)}/{len(G)}; matches {M}')
print('match masks 0->1 (+,-), 1->0 (+,-):',
      *(tuple(f'{v:06x}' for v in key) for key in F if F[key] in [(0,1),(1,0)]))

assert len(F.keys() & F.keys()) == 506
S = list(SIGMA)
S[0], S[1] = S[1], S[0]
H = signed_differences(masks(S))
assert F.keys() & H.keys() == set()
print('negative controls: identity matches 506; swapped coordinates 0,1 match 0')
