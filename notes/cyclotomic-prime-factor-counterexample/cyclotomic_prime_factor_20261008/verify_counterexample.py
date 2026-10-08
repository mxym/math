#!/usr/bin/env python3
"""Standalone exact certificate for Billey--Swanson Conjecture 48.

Only the Python standard library is used. Coefficients are in increasing order.
No floating point arithmetic, numerical roots, external software, or databases.
The counterexample is frozen as (Phi_4 Phi_9 Phi_25 Phi_30)^6, degree 216.
"""
from functools import cache
import hashlib
import json
from pathlib import Path

def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)

def power(a,n):
    b=[1]
    for _ in range(n):b=mul(b,a)
    return b

def divmod_monic(a,b):
    assert b[-1]==1
    a=trim(a);q=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        d=len(a)-len(b);v=a[-1];q[d]=v
        for j,c in enumerate(b):a[d+j]-=v*c
        a=trim(a)
    return trim(q),a

@cache
def cyclotomic(n):
    a=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d==0:
            a,rem=divmod_monic(a,cyclotomic(d))
            assert rem==[0]
    return tuple(a)

def prime(n):
    return n>=2 and all(n%d for d in range(2,__import__('math').isqrt(n)+1))

def main():
    factors={4:[1,0,1],9:[1,0,0,1,0,0,1],
             25:[1]+[0]*4+[1]+[0]*4+[1]+[0]*4+[1]+[0]*4+[1],
             30:[1,1,0,-1,-1,-1,0,1,1]}
    base=[1]
    for n,a in factors.items():
        assert list(cyclotomic(n))==a
        assert not prime(n)
        base=mul(base,a)
    assert len(base)==37 and base==base[::-1] and min(base)==0
    # Independent q-integer rational-form identity.
    numerator=[1];denominator=[1]
    for n in [4,9,25,30]:numerator=mul(numerator,[1]*n)
    for n in [1,6,10,15]:denominator=mul(denominator,[1]*n)
    assert mul(base,denominator)==numerator
    F=power(base,6)
    assert len(F)==217 and F[0]==F[-1]==1
    assert F==F[::-1] and min(F)==1 and sum(F)==30**6
    differences=[F[0]]+[F[j]-F[j-1] for j in range(1,109)]
    assert min(differences[1:])==5
    assert all(d>0 for d in differences)
    # A second reconstruction: positive centered q-integer decomposition.
    reconstruction=[0]*217
    for j,d in enumerate(differences):
        for i in range(j,217-j):reconstruction[i]+=d
    assert reconstruction==F
    # Independent finite prime-order divisor check, without using irreducibility.
    # Phi_p has degree p-1, so primes p>217 cannot divide degree-216 F.
    remainders={}
    for p in range(2,218):
        if prime(p):
            _,rem=divmod_monic(F,[1]*p)
            assert rem!=[0]
            remainders[str(p)]=rem
    data={'statement':'Counterexample to Billey--Swanson Conjecture 48',
          'factorization':{'4':6,'9':6,'25':6,'30':6},'degree':216,
          'base_coefficients_ascending':base,'coefficients_ascending':F,
          'centered_q_integer_weights':differences,
          'strict_increase_indices':[1,108], 'minimum_strict_difference':5,
          'coefficient_sum':sum(F),'maximum_coefficient':max(F),
          'prime_order_remainders':remainders,
          'verification':'All asserted identities and inequalities verified in exact integers.'}
    root=Path(__file__).resolve().parent
    path=root/'certificate.json';path.write_text(json.dumps(data,indent=2)+'\n')
    print('PASS: degree 216; strictly positive symmetric coefficients; unique peak at 108.')
    print('PASS: every first-half strict difference is positive; minimum is 5.')
    print('PASS: independent centered-q-integer reconstruction.')
    print('PASS: cyclotomic construction and q-integer rational-form identity.')
    print('PASS: no prime-order cyclotomic divisor; all possible primes checked exactly.')
    print('coefficient_sum =',sum(F),'peak =',max(F))
    print('certificate_sha256 =',hashlib.sha256(path.read_bytes()).hexdigest())

if __name__=='__main__':main()
