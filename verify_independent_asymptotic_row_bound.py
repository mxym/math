#!/usr/bin/env python3
"""Exact arithmetic controls for the independent asymptotic row lemma."""
from fractions import Fraction as F


def need(test, description):
    if not test:
        raise AssertionError(description)


for m in range(1,257):
    J=[F(i,2) for i in range(m-1,0,-2)]
    need(sum(t*t for t in J)==F(m*(m*m-1),24),("S_m",m))
    need(sum(t**4 for t in J)==F(m*(m*m-1)*(3*m*m-7),480),("T_m",m))
for d in range(1,257):
    x=F(5*d*d+1,24)
    next_point=(int(4*x)+1)/F(4)
    expected=(F(5,24),F(1,4),F(1,8),F(1,12),F(1,8),F(1,4))[d%6]
    need(next_point-x==expected,("quarter lattice gap",d))
    S2=F(2*d*(4*d*d-1),24)
    S1=F(d*(d*d-1),24)
    need((S2-3*S1)/d==x,("E_*",d))
    need(F(4,3)*(S2+5*S1)/d<=F(13,18)*d*d,("initial log bound",d))
constant=F(1,10)-F(7,320)-F(1,24)*F(5,6)-F(1,2)*F(5,24)**2
need(constant==F(25,1152), "signed coefficient")
need(F(1,24)+constant==F(73,1152)<F(1,12), "limiting lattice margin")
print("PASS: moments, quarter-lattice gaps and exact signed coefficient")
