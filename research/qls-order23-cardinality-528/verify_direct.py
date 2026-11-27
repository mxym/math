#!/usr/bin/env python3
"""Check all 46 bases and all 529 rays, over Q(sqrt(-23))."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product

# In the representation (a,b), (a,b) denotes a+b*sqrt(-23).
def mul(x,y):
    a,b = x
    c,d = y
    return (a*c - 23*b*d, a*d + b*c)

def conj(x):
    return x[0], -x[1]

def dot(u,v):
    terms = [mul(conj(a),b) for a,b in zip(u,v)]
    return tuple(sum(z) for z in zip(*terms))

I = (F(1), F(0))
O = (F(0), F(0))
Z = (F(-11,12), F(1,12))
assert mul(Z,conj(Z)) == I
# Independent closed data rather than regenerating the bit-set representation.
d = tuple(map(int,"01111010110011001010000"))
sig = (22,6,13,2,9,5,16,10,1,20,14,4,18,3,19,21,12,17,8,7,11,15,0)
u = range(23)
assert len(d) == 23 and sum(d) == 11
assert all(d[a] == int(a != 0 and pow(a,11,23) == 1) for a in u)
assert sorted(sig) == list(u)

def cells(s):
    return {(i,j): tuple(mul((I,Z)[d[(k-i)%23]],(I,Z)[d[(s[k]-j)%23]]) for k in u)
            for i,j in product(u,repeat=2)}

def ray_partition(c):
    rays = {}
    for ij,w in c.items():
        assert mul(w[0],conj(w[0])) == I
        dephased = tuple(mul(x,conj(w[0])) for x in w)
        rays.setdefault(dephased,[]).append(ij)
    return rays

c = cells(sig)
nbases = ng = 0
for iv in (False,True):
    for a in u:
        B = [c[b,a] if iv else c[a,b] for b in u]
        for b in u:
            for t in range(b,23):
                assert dot(B[b],B[t]) == ((F(23),F(0)) if t == b else O)
                ng += 1
        nbases += 1
r = ray_partition(c)
count = Counter(map(len,r.values()))
repeat = sorted(g for g in r.values() if len(g)>1)
assert count == {1:527,2:1} and repeat == [[(0,1),(1,0)]]
assert c[0,1] == c[1,0]
keys = [(ij, tuple(mul(x,conj(w[0])) for x in w)) for ij,w in c.items()]
checked = 0
equal = []
for (a,x),(b,y) in combinations(keys,2):
    checked += 1
    if x == y:
        equal.append((a,b))
assert checked == 139656 and equal == [((0,1),(1,0))]
print(f'direct exact Gram: {nbases} bases, {ng} upper-triangular entries')
print(f'direct exact rays: 529 cells, {checked} unordered pairs, {len(r)} rays, multiplicities {sorted(count.items())}, repeat {repeat}')

t = list(sig)
t[0], t[1] = t[1], t[0]
control = len(ray_partition(cells(u))),len(ray_partition(cells(t)))
assert control == (276,529)
print(f'negative controls: identity gives {control[0]} rays; swapped coordinates 0,1 give {control[1]} rays')
