"""Rational lower bound and independent log-graded subset-sum control."""
from fractions import Fraction as Q
from itertools import combinations
from math import factorial
def need(b, why):
    if not b: raise ValueError(why)
def logs(x):
    x=Q(x); t=(x-1)/(x+1); need(0<=t<1,'log domain')
    n=35
    b=sum((2*t**(2*k+1)/(2*k+1) for k in range(n)),Q(0))
    return b,b+2*t**(2*n+1)/((2*n+1)*(1-t*t))
h=sum((Q(1,j) for j in range(1,4097)),Q())
g=h-12*logs(2)[1]-logs(Q(4097,4096))[1]
need(g>Q(577,1000),'gamma lower')
eg=sum((Q(577,1000)**j/factorial(j) for j in range(12)),Q())
l=logs(Q(3,2))[0]
d=4*logs(2)[1]-1-Q(16,9)*l**4/6
need(d>0,'upper positive')
err=Q(300009*4,100*factorial(99))+Q(702,factorial(300))
bound=1-d/eg-err
need(bound>Q(90,10000),'reserve')
# Log weights in integer units of 1/20 log Z. Compare all actual subsets
# to the grouped formula, testing arbitrary additional primes in the gap.
for v in [(21,22,29,41),(23,24,30,50,33,36,61),(21,22,30,60,35,39),(25,26,27,41,37)]:
    u=sum((-1)**k*sum(c) for k in range(1,len(v)+1) for c in combinations(v,k) if sum(c)<=60)
    w=[x*(sum(y+x<=60 for j,y in enumerate(v) if i!=j)-1) for i,x in enumerate(v) if x<=60]
    need(u==sum(w),'marked expansion')
    need(sum(map(abs,w))-abs(u)>=80,'event triangle gap')
print('Same cubic bulk: strict reserve >0.0090 by rational inequalities.')
