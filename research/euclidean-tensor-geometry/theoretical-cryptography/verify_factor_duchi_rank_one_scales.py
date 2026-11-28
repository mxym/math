#!/usr/bin/env python3
"""Check the finite word identities used in the four-factor weighted rank-one note."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, prod
from random import Random

if not __debug__:
    raise RuntimeError("Normal mode, not -O, is required")

def edge(i,j):
    return tuple(sorted((i,j)))

def transitions(word):
    return tuple(sorted(edge(i,j) for i,j in zip(word,word[1:]) if i!=j))

V=tuple(range(4))
W=list(product(V,repeat=4))
perfect=(
    ((0,1),(2,3)), ((0,2),(1,3)), ((0,3),(1,2)),
)
edges=tuple(combinations(V,2))
for i,j in edges:
    got=Counter((word.count(i),len(transitions(word))) for word in W if set(word)=={i,j})
    assert got==Counter({(1,1):2,(1,2):2,(3,1):2,(3,2):2,
                         (2,1):2,(2,2):2,(2,3):2})
for i,l in permutations(V,2):
    j,k=[x for x in V if x not in (i,l)]
    got=Counter(transitions(word) for word in W
                if word.count(i)==2 and l not in word and len(set(word))==3)
    a,b,c=edge(i,j),edge(i,k),edge(j,k)
    expected=Counter(tuple(sorted(L)) for L in
                     [(a,b),(a,c),(b,c),(a,a,b),(a,b,b),(a,b,c)])
    assert got==Counter({p:2*x for p,x in expected.items()})
ham=Counter(transitions(w) for w in permutations(V))
by_match=Counter(tuple(sorted((a,b,e))) for a,b in perfect for e in edges if e not in (a,b))
assert ham==Counter({p:2*x for p,x in by_match.items()})
assert Counter(len(set(w)) for w in W)=={1:4,2:84,3:144,4:24}
assert [comb(4,l)*3**(4-l) for l in range(5)]==[81,108,54,12,1]

# Every sign check on beta is rational: beta is the positive root of
# 45 beta^2 - 28 beta - 12=0, and lies strictly between 9/10 and 1.
assert 45*F(9,10)**2-28*F(9,10)-12<0<45-28-12
assert 11*F(9,10)-8>0 and 24-9>0 and 19-F(40,9)>0

# Arithmetic sanity on abstract non-Gram overlap tables, not needed by the proof.
rng=Random(143)
for _ in range(175):
    scalars=[F(rng.randint(0,30),rng.randint(1,9)) for _ in V]
    R={e:F(rng.randint(0,90),100) for e in edges}
    val=lambda w:prod(scalars[i] for i in w)*prod(R[e] for e in transitions(w))
    r=sum(val(w) for w in W)
    s=sum(val(w) for w in permutations(V))/24
    d=sum(a**4 for a in scalars)/4
    assert r>=252*s+4*d
print("PASS exact word identities and rational overlap tests")
