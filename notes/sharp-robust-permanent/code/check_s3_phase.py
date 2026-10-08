#!/usr/bin/env python3
"""Exact replay for Section 10 of the robust permanent manuscript.

Checks a rational p=5/2 witness, the S3 parity intersection structure,
and symbolic equality kernels in Q(sqrt(3)). Not an infinite-p checker.
Requires Python >=3.9 and sympy.
"""
from fractions import Fraction as F
from itertools import permutations
from sympy import Matrix, diag, simplify, sqrt, symbols

# Proposition 7 / Corollary 8: a fully rational obstruction at p=5/2.
t = F(1009, 10000)
eps = F(1, 16)
a = F(1, 6) + t
b = F(1, 6) - t
assert t > 0 and b > 0
assert a == F(8027, 30000)
assert eps ** 2 == F(1, 256)
assert eps ** 5 == F(1, 16**5)
# eps^(5/2) = 1/1024 exactly; no fractional-power arithmetic.
norm_base_fifth = F(1, 3**6) * (1 + F(1, 1024))**4
lhs = a + b * eps**2
assert lhs == F(411377, 1536000)
assert a**5 < F(1, 3**6), "singleton constraint is not satisfied"
assert lhs**5 > norm_base_fifth, "two-row test does not violate"
print("PASS rational p=5/2: singleton passes, two-row inequality fails")

perms = list(permutations(range(3)))
def sign(pi):
    return 1 if sum(pi[i] > pi[j] for i in range(3)
                    for j in range(i+1,3)) % 2 == 0 else -1
evens = [pi for pi in perms if sign(pi) > 0]
odds = [pi for pi in perms if sign(pi) < 0]
assert len(evens) == len(odds) == 3
for e in evens:
    for o in odds:
        assert sum(e[i] == o[i] for i in range(3)) == 1
# Each even-odd pair is counted once in the three marginal entropy sums.
assert sum(sum(e[i] == o[i] for i in range(3))
           for e in evens for o in odds) == 9
print("PASS exact K3,3 incidence and S3 parity decomposition")

# Equality kernels of Theorem 6, for the positive determinant sign.
A = symbols('A', positive=True)
s = sqrt(3)
beta = 2 / s
k = 2*s - 3
h = s - 1
def M(u, v, w):
    return Matrix([[0,(2-beta)*w,beta*v],
                   [beta*w,0,(2-beta)*u],
                   [(2-beta)*v,beta*u,0]])
def H(u,v,w):
    return Matrix([[u*u+k*v*v,-h*u*v,-h*u*w],
                   [-h*u*v,v*v+k*w*w,-h*v*w],
                   [-h*u*w,-h*v*w,w*w+k*u*u]])
ones = Matrix([1,1,1])
kernel_constant = H(A,A,A)*ones
kernel_spike = H(A,0,0)*Matrix([0,1,0])
image_constant = M(A,A,A)*ones
image_spike = M(A,0,0)*Matrix([0,1,0])
assert all(simplify(x)==0 for x in kernel_constant)
assert all(simplify(x)==0 for x in kernel_spike)
assert all(simplify(image_constant[i]-2*A*ones[i])==0 for i in range(3))
assert all(simplify(image_spike[i]-(beta*A if i==2 else 0))==0 for i in range(3))
print("PASS exact S3 equality kernels: constant and even spikes")
print("SECTION 10 EXACT CHECKS PASSED")
