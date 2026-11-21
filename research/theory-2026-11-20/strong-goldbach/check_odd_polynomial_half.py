#!/usr/bin/env python3
"""Exact rank-profile identities; no numerical prime assumptions."""
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
from itertools import combinations
import random

def require(b,msg):
    if not b:
        raise ArithmeticError(msg)

@lru_cache(None)
def odd_coeff(k,D):
    if k==0:
        return F(int(D==0))
    return sum((odd_coeff(k-1,D-u)/u for u in range(1,D+1,2)),F(0))

def angular(k,D):
    return F(D*2**(k-1),factorial(k))*odd_coeff(k,D)

for D in range(1,36,2):
    require(sum(angular(k,D) for k in range(1,D+1,2))==D,('angular sum',D))
    require(angular(1,D)==1,('prime atom',D))
require(angular(3,3)==2 and angular(3,5)==F(10,3) and angular(5,5)==F(2,3),'sample angles')
require(F(9,4)*angular(3,3)-F(5,4)*angular(3,5)==F(1,3),'sample rank3 calibration')
require(F(5,4)*angular(5,5)==F(5,6),'adverse rank5 exact angular mass')
require(F(1,2)==F(9,4)*3-F(5,4)*5,'exact first-slope match')

def bits(a):
    sums=[(F(0),1)]
    for t in a:
        sums+= [(s+t,-m) for s,m in sums]
    return sums

r=random.Random(0xb70)
cnt=0
for k in range(2,10):
  for _ in range(32):
    z=[r.randint(1,500) for _ in range(k)]
    a=sorted(F(t,sum(z)) for t in z)
    amax=a[-1]
    for D in (3,5,7):
      sums=bits(a)
      half=sum(m*(1-2*s)**D for s,m in sums if s<F(1,2))
      if k%2:
        full=sum(m*(1-2*s)**D for s,m in sums)
        require(2*half==full,('literal odd complement',k,D))
        if k>D:
            require(half==0,('degree vanishing',k,D))
      if D==3 and k==3:
        require(half==24*a[0]*a[1]*a[2],'full cubic triple')
      if D==3 and amax>F(1,2):
        if k==2:
            require(half==1-(1-2*a[0])**3,'high cubic semi')
        if k==4:
            require(half==48*a[0]*a[1]*a[2],'high cubic rank4')
        if k>=5:
            require(half==0,'high cubic degree cutoff')
      cnt+=1
require(-3*20+6+23+3==-28,'absolute collar exponent')
print(f'{cnt} exact profile replays; odd-angle sums through degree 35; collar exponent -28')
