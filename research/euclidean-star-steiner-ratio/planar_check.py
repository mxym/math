"""Exact ancillary evaluation of the 12-term planar tangent. Run under Python -B -O."""
from fractions import Fraction as Q
from math import comb
def check(condition, name):
    if not condition: raise ArithmeticError(name)
a=Q(369,400)
cs=[Q(comb(4*j,2*j)*comb(2*j,j),(4*j-1)*2**(6*j)) for j in range(1,13)]
P=sum(c*a**(2*j) for j,c in enumerate(cs,1))
deriv=sum(2*j*c*a**(2*j-1) for j,c in enumerate(cs,1))
D=(1-P)/2-(1+a)*deriv
V=(1+a)*(1-P)+(1-a)*D
check(0 < D < Q(1,1600),'slope numerator')
check(0 < V < Q(17836,10000),'tangent numerator')
check(Q(17836,10000)**2 < (1+a)*Q(2573,2000)**2,'final squared comparison')
print('PASS: 12-term exact planar tangent; 0 < D < 1/1600, 0 < V < 17836/10000, V/sqrt(769/400) < 2573/2000.')
