"""Exact one-sided numerical checks; runs with python -O."""
from fractions import Fraction as Q
from math import factorial
def need(b):
    if not b: raise ArithmeticError("failed certified inequality")
def logs(x):
    x=Q(x); need(x>=1); z=(x-1)/(x+1); n=24
    low=2*sum((z**(2*k+1)/(2*k+1) for k in range(n)),Q())
    return low,low+2*z**(2*n+1)/((2*n+1)*(1-z*z))
def lo(x): return logs(x)[0]
def hi(x): return logs(x)[1]
c=lo(2)**2/2
for i in range(1,9):
    l=2+Q(i-1,8); v=2+Q(i,8)
    b=lo(2/(v-1))+(1-hi(v-1))*lo(l/2)
    need(b>=0); c+=b*lo(v/l)
need(c>Q(389,1000))
g=Q(1,100); eps=g; h=Q(3,2)
def gap(s): return Q(4,s*factorial(s-1))
err=(gap(30)/eps+gap(30)+gap(20)/h)/g
need(err<Q(1,1000000))
margin=((1-2*g)*Q(389,1000)-(1-1/h))/(2*g)-err
need(margin>Q(23,10))
print("Certified C0>0.389; sieve error<1e-6; asymptotic net lower>2.3 X_P.")
