"""Exact tests of the lattice proof; standard library only, no floating-point checks."""
from itertools import product
from fractions import Fraction
from collections import Counter
from math import gcd

def need(cond,why):
    if not cond: raise ArithmeticError(why)
def diff(p):
    return [sum(p[i]*p[i+j] for i in range(len(p)-j)) for j in range(len(p))]
def test(p):
    need(all(x>0 for x in p) and all(x*x>=y*z for y,x,z in zip(p,p[1:],p[2:])),'test input must be log-concave')
    n=len(p); W=sum(p); a=diff(p)
    s=sorted(a[:0:-1]+a,reverse=True); v=sorted([x*W for x in p]*2,reverse=True)
    s+=[0]*(len(v)-len(s))
    a0=a+[0]*(n+2)
    dacc=vacc=0
    for rank,(u,w) in enumerate(zip(s,v),1):
        dacc+=2*u; vacc+=w
        need(dacc>=vacc,(p,rank))
    need(dacc==vacc==2*W*W,p)
    need(2*max(s)>max(v),'strict first coordinate')
    for k in range(n+1):
        at=lambda i: p[i] if 0<=i<n else 0
        rng=range(-k,n)
        overlap1=sum(min(at(i),at(i+k)) for i in rng)
        overlap2=sum(min(at(i)*at(j+k),at(i+k)*at(j)) for i in rng for j in rng)
        need(overlap2==2*sum(a[k+1:])+a0[k],'product overlap')
        need(overlap2<=W*overlap1,'marginalization')
        largest=sum(sorted(p,reverse=True)[:k])
        need(largest==W-overlap1,'single crossing')
    return 1
N=0
for n in range(1,8):
  for p in product(range(1,7),repeat=n):
    if all(x*x>=y*z for y,x,z in zip(p,p[1:],p[2:])):
      N+=test(p)
# Further skewed, many-level and flat-top examples with very large exact integer weights.
for n in (2,5,10,17):
 for num,den in ((1,1),(2,3),(100,99),(1,13)):
  p=[num**i*den**(n-i-1) for i in range(n)]
  N+=test(p); s=sorted(p); N+=test(s+s[::-1])
# Negative control: four non-consecutive Sidon support sites, all weights one.
bad=[int(i in (0,1,4,10)) for i in range(11)]
d=diff(bad); need(sum(sorted(d[:0:-1]+d,reverse=True)[:8])<16,'invalid assumption unnoticed')
print(f'PASS: {N} finite log-concave pmfs, all ranks and shifts; non-log-concave control fails.')
