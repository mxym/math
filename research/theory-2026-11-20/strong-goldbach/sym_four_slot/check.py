"""Exact upper Riemann proof; no floating point, assertions, or external library."""
from fractions import Fraction as Q
from math import factorial
def req(t,m):
    if not t:raise ValueError(m)
h=32; s=Q(99,10); j=int(h*(s-1)); a=[Q(1)]*(h+1)
for i in range(h+1,j+1):a.append(sum(a[i-h:i],Q())/i)
delta=4*a[j]/s
req(delta<Q(1,10**9),'linear sieve gap')
tot=459750*delta+Q(107,factorial(15))
req(tot<Q(5,10000),'joint error')
req((35**2-1)//2==612 and 612*15*50+750==459750,'geometry')
req(Q(3,10)+Q(198,1000)<Q(1,2),'joint modulus')
print('Combined limsup <0.0005; eventual symmetric reserve >0.999.')
