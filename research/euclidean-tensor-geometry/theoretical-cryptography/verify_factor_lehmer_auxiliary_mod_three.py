#!/usr/bin/env python3
"""Exact certificate for an auxiliary-resultant Mahler gap modulo three."""
from fractions import Fraction as Q


def quad(x):
    return 24*x*x+17*x-5


def norm2_bound(lo,hi):
    return (2*(1-lo))**12*(2*(1+hi))**2*max(abs(1+2*lo),abs(1+2*hi))**10


def circle():
    intervals=[(Q(-931893,10**6),Q(-931892,10**6)),
               (Q(223559,10**6),Q(223560,10**6))]
    assert -1<intervals[0][0]<intervals[0][1]<Q(-1,2)
    assert Q(-1,2)<intervals[1][0]<intervals[1][1]<1
    for lo,hi in intervals:
        assert quad(lo)*quad(hi)<0
        assert norm2_bound(lo,hi)<218**2


def thresholds():
    # A^24=3^17/218 ; at d=8 losing a factor 3^(1/(2d))
    # raises to A^48/3^3=3^31/218^2. At d=54 use exponent 216.
    a24=Q(3**17,218)
    assert Q(203,125)**48<Q(3**31,218**2)<a24**2
    assert Q(17221,10000)**216<Q(3**151,218**9)<a24**9
    assert Q(17399,10000)**24<a24<Q(174,100)**24
    # The larger real trace root of t^2-t-3 equals rho+rho^-1.
    x=Q(17221,10000)
    t=x+1/x
    assert t>2 and t*t-t-3>0
    x=Q(17220,10000)
    t=x+1/x
    assert t>2 and t*t-t-3<0


def small_degrees():
    # If M<=rho<1.7221, all trace roots lie in [-T,T] in modulus.
    x=Q(17221,10000)
    T=x+1/x
    assert 2<T<Q(5,2) and 2*T<5 and T*T<6
    assert [i for i in range(-5,6) if i%3==2 and abs(i)<=2*T]==[-4,-1,2]
    assert [i for i in range(-6,7) if i%3==0 and abs(i)<=T*T]==[-3,0,3]
    # At B=-3, the a=-1 trace is rho's; for |a|>=2 a root exceeds T.
    assert T*T-2*T-3<0
    # At B=3, a=-4 has trace roots 1,3. The other two have Im^2>=2.
    assert (x-1/x)**2<2


if __name__=='__main__':
    circle();thresholds();small_degrees()
    print('PASS: both circle maxima, exact degree thresholds, and the low-degree bounds')
