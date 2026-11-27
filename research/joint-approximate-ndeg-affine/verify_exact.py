#!/usr/bin/env python3
"""Rational witness and independent optimal adaptive querying checks."""
from fractions import Fraction as Q
from functools import lru_cache


def L(e):
    return 1 + (2*e)//(1-e)


def eps(L):
    return Q(L-1,L+1)


def valid(value, b, label, e):
    return abs(value) >= 1 if label == b else abs(value) <= e


def pivot_label(z,w,a,b):
    return int(w<a) if z==0 else int(w>=b)


def minimax(a,b):
    s=a+b-1

    @lru_cache(None)
    def queries(z, ones, nleft):
        labels = {pivot_label(zz,w,a,b) for w in range(ones,ones+nleft+1)
                  for zz in ((0,1) if z==-1 else (z,))}
        if len(labels)==1:
            return 0
        candidates=[]
        if z==-1:
            candidates.append(1+max(queries(0,ones,nleft),queries(1,ones,nleft)))
        if nleft:
            candidates.append(1+max(queries(z,ones,nleft-1),queries(z,ones+1,nleft-1)))
        return min(candidates)

    return queries(-1,0,s)


witness_tests = 0
for a in range(1,9):
    for b in range(1,9):
        s=a+b-1
        assert L(eps(a))==a and L(eps(b))==b
        # Check the floor transition on both sides, including exact endpoints.
        assert L((eps(a)+eps(a+1))/2)==a
        assert a==1 or L((eps(a-1)+eps(a))/2)==a-1
        assert minimax(a,b)==s+1
        for z in (0,1):
            for w in range(s+1):
                label=pivot_label(z,w,a,b)
                p1=Q(2*w+2*a*z-2*a-b+1,b+1)
                p0=Q(2*w-2*b*z-a+1,a+1)
                assert valid(p1,1,label,eps(b))
                assert valid(p0,0,label,eps(a))
                witness_tests+=2
print(f"paired affine sharpness: 64 error pairs (closed boundaries), {witness_tests} rational witness values, minimax D=m for all 64")

# Test the approximate parity bounds in the truth-table/character basis,
# independently of the witness-normalization arguments.
parity_tests=0
for n in range(1,11):
    slow=[(-1)**(x.bit_count()) for x in range(1<<n)]
    for y in range((1<<n)-1):
        assert sum(slow[x]*(-1)**((x&y).bit_count()) for x in range(1<<n))==0
    left=(1<<(n//2))-1
    right=((1<<n)-1)^left
    for x in range(1<<n):
        A=(-1)**((x&left).bit_count())
        B=(-1)**((x&right).bit_count())
        assert ((A-B)//2)**2==x.bit_count()%2
        assert ((A+B)//2)**2==1-x.bit_count()%2
        parity_tests+=1
print(f"parity exact witness split and full-character orthogonality: {parity_tests} label pairs, n=1..10")

def T(d,x):
    a,b=Q(1),x
    for _ in range(d):
        a,b=b,2*x*b-a
    return a

# For this rational example d^2+1 points leave generous margin at epsilon=1/2;
# do not use floating point cosh/atanh as a checker.
cheby_vals=0
for d in range(1,17):
    m=d*d+1
    den=T(d,Q(m+1,m-1))
    assert den>=2
    for w in range(m+1):
        val=T(d,Q(m+1-2*w,m-1))/den
        assert valid(val,0,int(w!=0),Q(1,2))
        cheby_vals+=1
print(f"Chebyshev OR lower families: 16 exact rational recurrences, {cheby_vals} layer evaluations")
