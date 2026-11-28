#!/usr/bin/env python3
"""Small exact-arithmetic controls for DenseRandomLonelyRunner.md, not its asymptotic proof."""
from fractions import Fraction as F
from math import ceil, comb, floor, gcd
from collections import Counter


def layer_length(r, D, b):
    if not b:
        return F(abs(r) < D)
    return max(F(0), min(F(1), (D-r)/b)-max(F(0), (-D-r)/b))


def direct_count(N, t, delta):
    a, q = t.numerator, t.denominator
    return sum(F(min(a*v % q, -a*v % q), q) < delta for v in range(1,N+1))


def exact_hypergeom(n, s):
    assert 0 <= s <= n
    p = F(comb(2*n-s,n),comb(2*n,n))
    product = F(1)
    for j in range(s):
        product *= F(n-j, 2*n-j)
    assert p == product <= F(1,2**s)


scalar = 0
for d in range(1,65):
    D = F(d,16)
    for j in range(0,161):
        b = F(j,16)
        if D <= 1 and b <= 1:
            continue
        mass = sum(layer_length(r,D,b)
                   for r in range(floor(-D-b),ceil(D)+1))
        assert 2*mass >= 3*D, (D,b,mass)
        scalar += 1
assert sum(layer_length(r,F(1),F(2)) for r in range(-4,3)) == 2
assert sum(layer_length(r,F(2),F(0)) for r in range(-4,4)) == 3

# Exercise both branches, including rational times exactly at a forbidden boundary
# and both signs of the approximation error.
small, layers = 0, 0
for N in [18, 30, 84]:
    for q in range(1,15):
        for a in range(q):
            if gcd(a,q) != 1:
                continue
            for delta in [F(1,N),F(3,2*N),F(3,N),F(1,5),F(1,4)]:
                D = q*delta
                for b_signed in [F(-2),F(-1),F(-1,2),F(0),F(1,2),F(1),F(3,2),F(2),F(3)]:
                    t = F(a,q)+b_signed/(N*q)
                    b = abs(b_signed)
                    count = direct_count(N,t,delta)
                    if D <= 1 and b <= 1:
                        k = ceil(N*delta)-1
                        assert k*q <= N
                        assert all(abs(j*q*t-j*a) < delta for j in range(1,k+1))
                        assert count >= k
                        small += 1
                    else:
                        rs = list(range(floor(-D-b)+1,ceil(D)))
                        mass = sum(layer_length(r,D,b) for r in rs)
                        assert mass >= 3*D/2
                        assert abs(count-N*mass/q) <= 2*len(rs), (N,q,a,delta,b_signed)
                        layers += 1

crt = 0
for N,p,q in [(75,11,13),(128,13,17),(432,23,29),(491,31,37)]:
    assert p*q > N
    def sets(m):
        return [{v for v in range(1,N+1) if v % m in (0,j,m-j)} for j in range(1,(m+1)//2)]
    A,B = sets(p),sets(q)
    cnt = Counter(len(x & y) for x in A for y in B)
    assert max(cnt) <= 9
    expected = sum((len(A) if v%p==0 else 1)*(len(B) if v%q==0 else 1)
                   for v in range(1,N+1))
    assert sum(k*m for k,m in cnt.items()) == expected
    for j,E in enumerate(A,1):
        a = pow(j,-1,p)
        delta = F(3,2*p)
        assert E == {v for v in range(1,N+1) if min(a*v % p, -a*v % p) < p*delta}
        assert all(E & E2 == set(range(p,N+1,p)) for E2 in A if E2 is not E)
    crt += len(A)*len(B)

for n in range(1,41):
    for s in range(n+1):
        exact_hypergeom(n,s)
print(f"PASS: {scalar} scalar, {small} multiples, {layers} residue-layer, "
      f"{crt} CRT cross-tests, and 860 fixed-cardinality probabilities")
