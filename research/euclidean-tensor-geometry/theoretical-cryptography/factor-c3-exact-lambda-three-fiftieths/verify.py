#!/usr/bin/env python3
from fractions import Fraction
from itertools import combinations
from math import gcd, lcm, isqrt

def primes_upto(n):
    a = bytearray(b"\x01") * (n + 1)
    a[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            a[p*p:n+1:p] = b"\x00" * (((n-p*p)//p)+1)
    return [i for i in range(3, n+1) if a[i]]

def carmichael3():
    out = []
    for p,q,r in combinations(primes_upto(400), 3):
        R = p*q*r
        if all((R-1) % (z-1) == 0 for z in (p,q,r)):
            out.append((p,q,r))
    return out

C = carmichael3()
assert len(C) == 28
identity = 0
div_checks = 0
mult_checks = 0
nonsimple = 0

for p,q,r in C:
    R = p*q*r
    lam = lcm(p-1,q-1,r-1)
    g = gcd(gcd(p-1,q-1),r-1)
    a,b,c = (p-1)//g, (q-1)//g, (r-1)//g
    assert gcd(a,b) == gcd(a,c) == gcd(b,c) == 1
    L = a*b*c
    assert lam == g*L
    S = (R-1)//lam
    assert g*g < S < (g+1)*(g+1)
    J = S-g*g
    E = L*J
    assert E == a+b+c + g*(a*b+a*c+b*c)
    assert Fraction(g,J) < a < Fraction(9*g,2*J)
    assert a+b+c < Fraction(3*L*J*J,g*g)
    assert Fraction(R,g**3*L) <= Fraction(35,16)
    if a > 1:
        nonsimple += 1

    A = a*b
    assert A + g*L == A*r
    assert L % A == 0 and R % r == 0 and gcd(A,r) == 1
    fA = A + g*L
    for t in range(2,8):
        for mR in range(t):
            for mL in range(t):
                Q = (r**mR)*(A**mL)
                for i in range(t):
                    v = (fA**i)
                    v *= R**max(mR-i,0)
                    v *= L**max(mL-i,0)
                    assert v % Q == 0
                    div_checks += 1
    identity += 1

    for kp in range(1,4):
      for kq in range(1,4):
       for kr in range(1,4):
        odd = p**kp*q**kq*r**kr
        lamodd = lcm(p**(kp-1)*(p-1),
                     q**(kq-1)*(q-1),
                     r**(kr-1)*(r-1))
        for e in range(0,9):
            lam2 = 1 if e <= 2 else 2**(e-2)
            lamN = lcm(lamodd,lam2)
            D = gcd(odd,lamN)
            assert D == odd//R
            B = lamN//D
            z = 0
            while B % 2 == 0:
                z += 1
                B //= 2
            assert any((2**j)*B == lam for j in range(z+1))
            mult_checks += 1

# Exact worst-point margin.
gamma = Fraction(53,350)
tau = Fraction(117,350)
ell = Fraction(191,350)
mu = Fraction(127,350)
margin = mu*mu + tau*tau/ell - tau
assert margin == Fraction(50339,23397500)
assert margin > Fraction(1,500)

# Exact grid check of the idealized parameter split.  The proof uses the
# derivative signs; this is only a finite regression companion.
grid_checks = 0
delta = Fraction(3,50)
for k in range(0,1001):
    gam = Fraction(3,25) + (Fraction(7,40)-Fraction(3,25))*k/1000
    ell0 = 1-3*gam
    tauc = min(3*gam-2*delta, 1-delta-4*gam)
    mu0 = 1-2*gam-tauc
    G = mu0*mu0 + tauc*tauc/ell0 - tauc
    assert G >= margin
    grid_checks += 1

print(f"C3 triples below 400: {len(C)}")
print(f"nonsimple examples: {nonsimple}")
print(f"normal-form identity cases: {identity}")
print(f"two-modulus divisibility checks: {div_checks}")
print(f"multiplicity/even-part checks: {mult_checks}")
print(f"exact parameter grid checks: {grid_checks}")
print(f"worst idealized margin: {margin} = {float(margin):.12f}")
print("PASS")
