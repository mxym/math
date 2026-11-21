#!/usr/bin/env python3
"""Exact finite support/sign checks; works with Python -O."""
from fractions import Fraction as F
from itertools import combinations_with_replacement, combinations


def require(v, data):
    if not v:
        raise AssertionError(data)


def score(ts, cut):
    T = S = 0
    for j in range(len(ts)+1):
        for a in combinations(ts, j):
            if sum(a) < cut:
                w = (-1)**j
                T += w
                S += 2*w*sum(2*v>=cut for v in a)
    return T,S


def run():
    Q = M = 0
    for k in (2,3,4):
        for ps in combinations_with_replacement(range(1,51),k):
            m = sum(ps)
            if 86<=m<=90:
                T,_ = score(ps,F(m)-F('50.1'))
                require(T<=1,(ps,T))
                Q+=1
            if m!=100:
                continue
            for cutoff in map(F,['48','48.5','49','49.5','49.99']):
                if k in (3,4) and max(ps)<cutoff:
                    T,S=score(ps,cutoff)
                    require(S<=T<=0,(ps,T,S,cutoff))
                    for a in (-10,-3,0,1):
                        require(S+a*(T-S)<=0,(ps,T,S,cutoff,a))
                    M+=1
    q = tuple(map(F,['.176']*5))
    Tq,_=score(q,F('.379'))
    Tm,S=score(tuple(map(F,['.321','.334','.345'])),F('.499'))
    require((Tq,Tm,S,S+Tq*(Tm-S))==(6,-2,-6,18),(Tq,Tm,S))
    Tm,S=score(tuple(map(F,['.33','.67'])),F('.499'))
    require((Tm,S,S+Tq*(Tm-S))==(0,-2,10),(Tq,Tm,S))
    require(3*F('.3592')>F('.900'),'mark multiplicity')
    require(1-F('.4992')<F('.501'),'remaining cofactor cap')
    require(F('.4994')+F('.0004')<F('.500'),'fixed lower-sieve level')
    require(F('.4992')-F('.140')>F('.354'),'source and mark disjoint')
    require(Q>0 and M>0,(Q,M))
    print(f'checked {Q} quotient signs, {M} reflected rank/cutoff signs, and two surviving adverse profiles')


if __name__=='__main__':
    run()
