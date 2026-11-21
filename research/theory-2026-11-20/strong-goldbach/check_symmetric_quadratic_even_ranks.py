#!/usr/bin/env python3
"""Exact finite sign/reciprocity checks and a rational bound for the tilt exponent."""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement


def require(ok, context):
    if not ok: raise AssertionError(context)


def divisor_rows(ps):
    return [(sum(a),(-1)**j) for j in range(len(ps)+1) for a in combinations(ps,j)]


def run():
    cases=0
    g=lambda t:8*t*(1-t)
    for k in (2,3,4,5,6):
        for ps in combinations_with_replacement(range(1,24),k):
            if sum(ps)!=40: continue
            rows=divisor_rows(ps)
            for B in (F('20.01'),F('20.2'),F('20.4')):
                z=40-B
                T=sum(c for t,c in rows if t<z)
                S=sum(c*g(F(t,40)) for t,c in rows if t<z)
                if max(ps)>B and k>=4: require(S==0,(ps,B,S))
                if max(ps)>B and k in (2,3): require(S<=0,(ps,B,S))
                if max(ps)<=B and k==3: require(S<=T<=0,(ps,B,T,S))
                if k>=4 and not k%2:
                    band=sum(c*g(F(t,40)) for t,c in rows if z<=t<=B)
                    require(2*S==-band,(ps,B,S,band))
                cases+=1
    # ln12 = ln3 + 2 ln2, using ln y = 2 sum z^(2j+1)/(2j+1), z=(y-1)/(y+1).
    def ln_upper(y):
        z=F(y-1,y+1); J=18
        return 2*sum(z**(2*j+1)/F(2*j+1) for j in range(J))+2*z**(2*J+1)/(F(2*J+1)*(1-z*z))
    u=ln_upper(3)+2*ln_upper(2)
    require(u<F('2.485'),u)
    require(-20+6+F(46,12)+4*u<F('-.22'),u)
    require(cases>0,cases)
    print(f'{cases} exact quadratic rank/cutoff tests; tilt exponent < -0.22')


if __name__=='__main__': run()
