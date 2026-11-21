#!/usr/bin/env python3
"""Finite exact controls for the elementary order-partition argument."""
from math import gcd,isqrt
def check(b,s):
    if not b:raise ValueError(s)
def primes(n):
    return [i for i in range(2,n+1) if all(i%j for j in range(2,isqrt(i)+1))]
def ordmod(m,r):
    z=m%r;d=1
    while z!=1:z=z*m%r;d+=1
    return d
ps=primes(179);parts=0
for m in range(3,26):
    for e in range(1,25):
        W=m**(2*e)-1
        for T in [2,7,31,89,179]:
            by={}
            for r in ps:
                if r<=T and W%r==0:
                    d=ordmod(m,r);check((r-1)%d==0 and 2*e%d==0,'order divisibility')
                    by.setdefault(d,[]).append(r)
            for d,rr in by.items():
                check(len(rr)<=T//d,'progression bound')
                check(2**len(rr)<=m**d-1,'distinct divisor bound')
                check(all((m**d-1)%r==0 for r in rr),'order support')
                parts+=1
# Bozek's genuine two-label EAC: A=[[0,3],[7,0]] when ordered 3,13,
# N-3=13^3, N-13=3^7. Det(I-A)=-20 and gcd of entries is 1.
n=2200
check(n-3==13**3 and n-13==3**7 and pow(3,40,n)==1,'actual center')
# A genuine signed-unit exponent need not kill the sign before squaring.
check(pow(3,20,n)==1 or pow(3,20,n)==n-1,'signed fraction')
# Direct example of sign loss in a unit quotient (not an EAC).
check(pow(3,2,10)==9 and pow(3,4,10)==1,'sign control')
print('order buckets checked:',parts,'genuine 2200 and signed-unit controls: PASS')
