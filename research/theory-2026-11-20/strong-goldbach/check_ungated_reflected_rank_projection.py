#!/usr/bin/env python3
"""Exact replay of the integer cutoff, repeat cases, rank signs, and numerical rails.

This tests only finite algebraic claims; it does not test the analytic bounds.
"""
from fractions import Fraction
from itertools import combinations_with_replacement
from math import prod


def require(truth, data):
    if not truth:
        raise AssertionError(data)


def factors_squarefree(primes):
    divs = [(1, 1)]
    for p in sorted(set(primes)):
        divs += [(p*d, -sign) for d, sign in divs]
    return divs


def main():
    cases = high = equal = rank2 = rank3 = repeated = 0
    for k in range(1, 7):
        for ps in combinations_with_replacement((2, 3, 5, 7, 11, 13, 17, 19, 23), k):
            m = prod(ps)
            ds = factors_squarefree(ps)
            # The physical proof needs only B^2>m and m/B>1. Check
            # strict boundaries B=m/d and generic points in the same cells.
            for d, _ in ds:
                for B in (Fraction(m, d), Fraction(2*m + 1, 2*d), Fraction(2*m - 1, 2*d)):
                    if not 1 < B < m or B*B <= m:
                        continue
                    cases += 1
                    T = sum(sign for d0, sign in ds if B*d0 < m)
                    if B*d == m:
                        equal += 1
                    if k > len(set(ps)):
                        repeated += 1
                    if k == 1:
                        require(T == 1, (ps, B, T))
                    if k > 1 and max(ps) > B:
                        require(T == 0, (ps, B, T))
                        high += 1
                    if k == 2 and max(ps) <= B:
                        require(T == 1 and min(ps)*B >= m, (ps, B, T))
                        rank2 += 1
                    if k == 3 and max(ps) <= B and B*B*B < m*m:
                        eligible = sum(B*p < m for p in set(ps))
                        require(eligible >= 1 and T == 1-eligible and T <= 0, (ps, B, T))
                        rank3 += 1
    require(min(cases, high, equal, rank2, rank3, repeated) > 0, 'empty test class')
    F = Fraction
    require(F(14,100) + F(86,100)*F(4,10) == F(484,1000), 'ordinary BV rail')
    require(F(1) - F(51,100) - F(14,100) == F(35,100), 'minimum free exponent')
    require(F(51,100) + 2*F(1,1000) < 1, 'rank-three active-prime count')
    for i in range(1, 100):
        epsilon = F(i,10000)
        b = F(1,2)+epsilon
        c_f = min(F(1,2000), epsilon/2)
        require(1-b+c_f < F(1,2), (epsilon, c_f))
        require(b + 2*c_f < 1, (epsilon, c_f))
    print(f'checked {cases} cutoffs: {high} high, {equal} strict equalities, '
          f'{rank2} rank-two survivors, {rank3} rank-three, {repeated} repeated-factor cases')


if __name__ == '__main__':
    main()
