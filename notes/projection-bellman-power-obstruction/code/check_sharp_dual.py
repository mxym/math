#!/usr/bin/env python3
"""Exact sharp solution of the infinite even-power LP restricted to 3 attainable
self-product tests. Solves a rational 3x3 dual/primal system; proves all
remaining infinitely many power columns strictly inactive.
"""
from fractions import Fraction as F
from check import SAMPLES,delta_power,log_bounds,sample_multiplier,require

POWERS=(2,4,8)
SHARP_FLOOR=F(486139,10**7)


def determinant(A):
    return (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1])
          - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0])
          + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0]))


def solve(A,b):
    d=determinant(A)
    require(d!=0,'three-case moment matrix singular')
    result=[]
    for j in range(3):
        E=[[b[i] if h==j else A[i][h] for h in range(3)] for i in range(3)]
        result.append(determinant(E)/d)
    return result


def transpose(A):return [[A[j][i] for j in range(3)] for i in range(3)]


def check():
    A=[[delta_power(r,h,p) for p in POWERS] for r,h in SAMPLES]
    y=solve(transpose(A),[F(1)]*3)
    require(all(q>0 for q in y),'rational moment dual weights not positive')
    for j in range(3):
        require(sum(y[i]*A[i][j] for i in range(3))==1,
                'support-column dual equality does not hold')

    for k in range(1,7):
        p=2*k
        val=sum(y[i]*delta_power(r,h,p) for i,(r,h) in enumerate(SAMPLES))
        require(val<=1 and (val==1)==(p in POWERS),
                f'invalid equality/strict complementarity at even exponent {p}')
    # For every p=2k>=14, elementary monotone powers dominate all columns.
    y1,y2,y3=y
    tail=11*y1-y2-y3+20*y2*F(5,7)**13+F(133,4)*y3*F(133,296)**13
    require(tail<1,'analytic infinite tail not strict')

    # Inverse of the moment matrix: Cramer's rule with canonical rationals.
    invcols=[solve(A,[F(i==j) for i in range(3)]) for j in range(3)]
    inverse=[[invcols[j][i] for j in range(3)] for i in range(3)]
    log_interval_list=[log_bounds(sample_multiplier(r,h)) for r,h in SAMPLES]
    a_intervals=[]
    for row in inverse:
        lo=sum(t* (log_interval_list[j][0] if t>=0 else log_interval_list[j][1]) for j,t in enumerate(row))
        hi=sum(t* (log_interval_list[j][1] if t>=0 else log_interval_list[j][0]) for j,t in enumerate(row))
        require(lo>0 and lo<=hi,'sharp primal moment coefficients must be positive')
        a_intervals.append((lo,hi))
    weighted_lo=sum(y[i]*v[0] for i,v in enumerate(log_interval_list))
    weighted_hi=sum(y[i]*v[1] for i,v in enumerate(log_interval_list))
    require(weighted_lo>SHARP_FLOOR,
            'sharp 3-state LP floor cannot be certified at requested threshold')
    require(sum(t[0] for t in a_intervals) <=weighted_hi and
            sum(t[1] for t in a_intervals)>=weighted_lo,
            'strong duality/primal sum intervals are inconsistent')
    print('PASS: exact SHARP infinite-power three-state Bellman linear programme')
    print('rational dual moments solve M^T w = (1,1,1), all weights positive')
    print('unique primal support degrees =',POWERS)
    print('all nonsupport even degrees strictly inactive, including entire infinite tail')
    print('all three primal optimum coefficients strictly positive (rigorous log intervals)')
    print('exact optimal restricted floor = sum_i w_i log(h_i*binom(2r_i,r_i)/4^r_i)')
    print('this exact floor exceeds',SHARP_FLOOR)
    print('does NOT assert sharpness of the full geometric Bellman coefficient problem')
    print('all tests use rational determinants, exact powers and rational logarithm remainders')


if __name__=='__main__':check()
