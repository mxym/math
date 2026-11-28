#!/usr/bin/env python3
"""Exact finite s=k+1 brackets for the equal-offset collision theorem."""
from fractions import Fraction
from math import prod


def need(test, name):
    if not test:
        raise AssertionError(name)


def numerator(k, n, L):
    return prod(n+2*j+1 for j in range(k+1))-L*prod(n-j for j in range(k))


def finite():
    expected=(10,41,125,335,829,1961,4497,10103,22361,48952,
              106260,229101,491203,1048214,2227814,4718131,9960957,20970948)
    got=[]
    for k in range(2,20):
        L=(k+1)*2**(k+1)
        lo,hi=2*k+3,L
        need(numerator(k, lo, L)<0<numerator(k, hi, L), ("initial bracket",k))
        while hi-lo>1:
            m=(lo+hi)//2
            sign=numerator(k, m, L)
            need(sign!=0, ("integer root",k,m))
            if sign<0:
                lo=m
            else:
                hi=m
        need(numerator(k, lo, L)<0<numerator(k, hi, L), ("final bracket",k))
        got.append(lo)
    need(tuple(got)==expected,"finite brackets differ")
    print("s=k+1: strict consecutive-integer brackets k=2,...,19",got)


def constants():
    # Two geometric tails in the moderate-shift counting lemma.
    near=Fraction(53,100)
    theta=Fraction(29,50)
    prime=Fraction(21,40)
    need(theta>prime and near>prime, "exponent order")
    need(1-theta<Fraction(1,2), "number of possible multipliers")
    need(near+1-theta<1, "arc width tends to zero")
    need(3*near/2-Fraction(1,2)==Fraction(59,200),
         "first counting exponent")
    need(2*near-theta==Fraction(12,25)<Fraction(1,2),
         "second counting exponent")
    need(3*(1-prime)>1, "reflected-index comparison")
    # Monotone bounds after the chosen finite cutoff k=20.
    need(Fraction(42*20**3,2**21)<1, "integer-gap error")
    need(Fraction(5,4)**3<2, "integer-gap error decreases for k >= 4")
    need(18+Fraction(9,4)+Fraction(3,16)<21, "upper error coefficient")
    need(2**20>=2*21, "exponential half-length dominates")
    print("PASS: exact rational inequalities in the proof")


if __name__=="__main__":
    finite()
    constants()
