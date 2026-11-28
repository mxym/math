#!/usr/bin/env python3
"""Circle covering test for the three fixed pentagon directions, in units of 6 degrees."""
from itertools import accumulate
from math import comb
def comps(v,k):
 if k==1:
  yield (v,);return
 for x in range(v+1):
  for tail in comps(v-x,k-1):yield (x,)+tail
def check():
 for n in range(1,7):
  turn=60*n;slack=n*(60-10*n);threshold=6*n;ct=0;best=turn
  for vv in comps(slack,n):
   g=[10*n+a for a in vv];points=list(accumulate(g,initial=0))[:-1]
   z=sorted((a+o)%turn for a in points for o in (0,18*n,36*n))
   gap=max([b-a for a,b in zip(z,z[1:])]+[z[0]+turn-z[-1]])
   if gap<threshold:raise AssertionError((n,g,gap,threshold))
   best=min(best,gap);ct+=1
  assert ct==comb(slack+n-1,n-1)
  print('circular covering',n,ct,best,'/',n,'six-degree units',flush=True)
if __name__=='__main__':check()

# Purely symbolic-free consistency checks for the quarter-turn orbit count:
# these algebraic identities follow by multiplying the displayed polynomials.
from fractions import Fraction as Q
assert Q(9,5)*Q(2,3)**2<1  # d>=4 cap packing; pi<10/3
assert Q(9,10)>Q(17,18)**2  # d=3 cap-avoidance threshold
for k in range(1,8):
    h=16*comb(k,2)
    for d,total in enumerate((4*k+h,12*k+h,4+20*k+h,12+28*k+h)):
        n=2*k+d
        assert total==2*n*(n-1)
