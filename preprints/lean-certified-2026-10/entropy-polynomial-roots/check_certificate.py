#!/usr/bin/env python3
"""Exact integer verifier for the (11,10) counterexample to Wakhare Conj. 2.
Python 3.8+ standard library only. No floating point, CAS, or root finder.
"""
from math import comb, gcd

if not __debug__:
    raise SystemExit("Run this verifier without Python -O or -OO.")

P = [1,352705,60632419,1227099358,6330005947,10701243741,
     6330005947,1227099358,60632419,352705,1]
Q = [11,1939817,289126442,5380098482,25959010187,41238382790,
     22851341183,4098130058,181139618,831413,-1]

# Multiply the defining rational coefficient sum by L=lcm(1,...,11).
L = 1
for j in range(1,12):
    L = L*j//gcd(L,j)
for r, coeff, scale in [(11,P,1),(10,Q,11)]:
    for j in range(11):
        numerator = sum((-1)**(j-v)*(L//(v+1))*comb(r*v+11,11)*comb(11,j-v)
                        for v in range(j+1))
        assert numerator*scale == L*coeff[j]

# z^10(1+z) is strictly increasing on z>0.
assert 117**10*242-125**11 == -90074807210933370467 < 0
assert 937**10*1937-1000**11 == 10474898608767871728104442364513 > 0

def hom(c,a,b):
    return sum(c[j]*a**j*b**(10-j) for j in range(11))

checks = [(1,5,919,-1),(2,5,1131,1),(3,5,935,-1),
          (2,3,938,1),(4,5,928,-1)]
signs = []
for a,b,u,direction in checks:
    assert 0<a<b
    N = 10*(b**11-a**11)**11*hom(Q,a**10,b**10)
    D = 121*b*(b**10-a**10)**11*hom(P,a**11,b**11)
    assert N>0 and D>0
    residual = direction*(1000*N-u*D)
    assert residual>0
    if direction<0:
        assert 125*u < 117*1000
        signs.append(1)
    else:
        assert u>937
        signs.append(-1)
    print(f'x={a}/{b}: sign(p)={signs[-1]:+d}; positive residual={residual}')
assert signs == [1,-1,1,-1,1]
assert all(checks[i][0]*checks[i+1][1] < checks[i+1][0]*checks[i][1]
           for i in range(4))
print('PASS: source coefficients, alpha bracket, and five strict signs.')
print('By continuity, at least four distinct roots lie in (0,1).')
