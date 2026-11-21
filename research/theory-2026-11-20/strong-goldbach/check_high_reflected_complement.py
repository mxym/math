#!/usr/bin/env python3
"""Exact finite profile tests for complementary quotient counts and positivity."""
from itertools import combinations, combinations_with_replacement
from fractions import Fraction as F


def require(ok, state):
    if not ok: raise AssertionError(state)


def score(ps, cutoff):
    return sum((-1)**k for k in range(len(ps)+1)
               for comb in combinations(ps,k) if sum(comb)<cutoff)


def run():
    # Scaled exponents, not a claim about available primes in tiny intervals.
    # D/a and decision endpoints include strict and weak bounds.
    delta,z,gap,B = 12, 1, 10, F('50.1')
    cts=[0,0,0]
    for k in range(2,6):
        for ps in combinations_with_replacement((2,3,5,9,10,11,12,13,21,28,35,40,47,50,51,54,62,65,71,74,78),k):
            q=sum(ps)
            if not 86<=q<=90: continue
            U=int(ps[-1]>B)
            V=sum(q-u>B and (z<u<=gap or u>delta) for u in ps)
            if min(ps)>delta:
                require(U<=V,(ps,U,V)); cts[0]+=1
            if U>V:
                require(U==1 and V==0 and all(gap<u<=delta for u in ps[:-1]),(ps,U,V))
                cts[1]+=1
            for cutoff in (F('11.2'),F(12)):
                C=score(ps,cutoff)
                if U>V: require(C<=1,(ps,C,U,V))
                if C<0: require(sum(u<cutoff for u in ps)>=2,(ps,C))
                cts[2]+=1
    require(all(cts),cts)
    require(F('.4995')<(1-F('.0005'))/2,'short reflected cofactor BV gap')
    require(F('.499')+F('.5')<1,'double pair cofactor reserve')
    print(f'{cts[0]} macro, {cts[1]} gap, {cts[2]} signed score checks')


if __name__=='__main__': run()
