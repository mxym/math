#!/usr/bin/env python3
"""Exact integer and rational checks of the signed tag and source counts."""
from fractions import Fraction
from itertools import product
from math import comb


def subsets(x):
    s = x
    while True:
        yield s
        if s == 0:
            break
        s = (s-1) & x


def count_check():
    pairs = projections = 0
    for n in range(2,9):
        for t in range(2,n+1):
            masks = [i for i in range(1<<n) if i.bit_count() < t]
            # Solve the upper-set equations by descending substitution,
            # separately from computing the closed binomial expression.
            solution = {}
            for d in sorted(masks,key=int.bit_count,reverse=True):
                solution[d] = 1-sum(c for k,c in solution.items() if k&d == d)
            formula = {d:(-1)**(t-1-d.bit_count())
                       *comb(n-d.bit_count()-1,t-1-d.bit_count()) for d in masks}
            assert formula == solution and all(x != 0 for x in formula.values())
            nr = sum(abs(x) for x in formula.values())
            assert nr >= 3 and nr%2 == 1
            gp = sum(x for x in formula.values() if x > 0)
            gm = sum(-x for x in formula.values() if x < 0)
            assert (gp,gm)==((nr+1)//2,(nr-1)//2)
            assert nr <= 3*gm
            if t == 2:
                assert nr == 2*n-1
            if t == 3:
                assert nr == 2*(n-1)**2-1
            if t == n:
                assert nr == (1<<n)-1
            for j in masks:
                plus,minus={},{}
                for d,x in formula.items():
                    r = d&j
                    dst = plus if x > 0 else minus
                    dst[r] = dst.get(r,0)+abs(x)
                for r in subsets(j):
                    assert plus.get(r,0)-minus.get(r,0)==int(r==j)
                    projections += 1
            # A one-copy perturbation is not a valid projected solution.
            changed = dict(formula)
            changed[0] += 1
            j = (1<<(t-1))-1
            assert sum(v for d,v in changed.items() if not d&j) == 1
            pairs += 1
    return pairs,projections


def two_index_minimax(c):
    a,b = (c+1)//2,(c-1)//2
    # All possible sums of f-induced signs in each disjoint label group.
    # Every value at each parity-compatible lattice point is realizable.
    atom = [(x,y) for x in range(-a,a+1,2) for y in range(-b,b+1,2)]
    optimum = Fraction(1,2)
    tested = 0
    for u,v in product(atom,repeat=2):
        worst = max(Fraction(abs(u[i]+v[j]),2*((a,b)[i]+(a,b)[j]))
                    for i,j in product(range(2),repeat=2))
        optimum = min(optimum,worst)
        tested += 1
    assert optimum == Fraction(1,2*c)
    return tested


def width_checks():
    total = 0
    for q in (2,4,8,16,32):
        for L in range(q,3*q+1):
            words_in_bucket = L//2
            # Linear objective on laws with atoms <=1/q:
            # all-extremal bucket counts come from uniform q-subsets.
            kmin,kmax = max(0,q-(L-words_in_bucket)),min(q,words_in_bucket)
            err = max(abs(Fraction(k,q)-Fraction(1,2)) for k in (kmin,kmax))
            assert err == min(Fraction(1,2), Fraction((L-q+1)//2,q))
            for c in (3,5,7,17,31):
                threshold = 1 if q <= 2*c else (q+2*c-1)//(2*c)
                if L < q+2*threshold-1:
                    assert err < Fraction(1,2*c)
                else:
                    assert err >= Fraction(1,2*c)
            total += 1
    return total


if __name__ == "__main__":
    pairs,projections = count_check()
    minimax = sum(two_index_minimax(c) for c in (3,5,7,17,31))
    print(f"exact PASS: {pairs} integer threshold instances; {projections} full tag-projection counts")
    print(f"exact PASS: {minimax} two-index sign-sum assignments; optimal bit errors and parity controls")
    print(f"exact PASS: {width_checks()} fixed-width alphabet/bias rounding cases")
