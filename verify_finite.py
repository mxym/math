#!/usr/bin/env python3
"""Fixed finite identities and a small witness; no asymptotic claims."""
from fractions import Fraction as Q
from math import factorial, prod

primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
count = 0
for a, p in enumerate(primes):
    for b in range(a + 1, len(primes) + 1):
        segment = primes[a:b]
        n = prod(segment)
        sigma = prod(q + 1 for q in segment)
        mertens_step = prod(Q(q, q - 1) for q in segment)
        square_correction = prod(1 - Q(1, q * q) for q in segment)
        assert Q(sigma, n) == mertens_step * square_correction
        # Exact finite version of the tail-loss comparison; 1 - product
        # is at most the sum of losses, and 1/q^2 < 1/(q(q-1)).
        assert 0 <= 1 - square_correction <= sum(Q(1,q*q) for q in segment)
        assert sum(Q(1,q*q) for q in segment) < Q(1,p-1)
        count += 1
assert count == 136

# p=2, n=30 and A=1/6 give one small verified witness.
# The exp Taylor sum is a strict lower bound for exp(7/2).
assert prod((2,3,5)) == 30 and prod((3,4,6)) == 72 > 60
assert sum(Q(7,2)**k / factorial(k) for k in range(9)) > 30
assert Q(3,2)**2 > 2
assert Q(7,2) == 4 - Q(1,6)*2*Q(3,2)
print("PASS: 136 exact squarefree interval identities and one rationally certified small witness")
