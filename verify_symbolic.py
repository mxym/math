#!/usr/bin/env python3
"""Exact polynomial arithmetic on fixed synthetic offset cells."""
from collections import Counter

# Polynomials in (t,D), represented by their exponent pairs.
def mul(f,g):
    h = Counter()
    for (i,j), a in f.items():
        for (k,l), b in g.items():
            h[i+k,j+l] += a*b
    return +h

def power(f,k):
    h = Counter({(0,0):1})
    for _ in range(k):
        h = mul(h,f)
    return h

def linear(a):
    return Counter({(1,0):1,(0,1):a})

U = ((0,1),(2,3))
V = ((0,2),(1,3))

def blocks(base,pattern):
    return [mul(linear(base+i),linear(base+j)) for i,j in pattern]

assert mul(*blocks(0,U)) == mul(*blocks(0,V))
assert set(U).isdisjoint(V)
for k in range(1,17):
    left = sum((power(f,k) for f in blocks(0,U)),Counter())
    right = sum((power(f,k) for f in blocks(0,V)),Counter())
    assert left[2*k,0] == right[2*k,0] == 2
    assert left[2*k-1,1] == right[2*k-1,1] == 6*k
    delta = left.copy()
    delta.subtract(right)
    assert all(i<=2*k-2 for (i,j),c in delta.items() if c)
    if k==1:
        assert (+delta) == Counter({(0,2):3}) and not (-delta)

# Three full identities using the two parity classes of 0..31.
A = [j for j in range(32) if bin(j).count("1")%2==0]
B = [j for j in range(32) if j not in A]
assert all(sum(j**k for j in A)==sum(j**k for j in B) for k in range(5))
for k in range(1,4):
    P = [f for j in A for f in blocks(4*j,U)] + [f for j in B for f in blocks(4*j,V)]
    Q = [f for j in A for f in blocks(4*j,V)] + [f for j in B for f in blocks(4*j,U)]
    assert sum((power(f,k) for f in P),Counter()) == sum((power(f,k) for f in Q),Counter())
print("PASS: 16 local moment degrees and 3 exact aggregate polynomial identities")
