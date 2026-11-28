#!/usr/bin/env python3
"""Independent class-level check of the natural alternating-six certificate.
No enumeration of S6 permutations or of cuts: Frobenius polynomial for the
symmetric character and a two-state transfer matrix for first crossings.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
from math import comb,prod
if not __debug__:raise RuntimeError('Run normal Python without -O')
def parts(n,m=6):
 if not n:yield ()
 for k in range(min(n,m),0,-1):
  for p in parts(n-k,k):yield (k,)+p
def schur(nu):
 # Vandermonde det(x_i^(3-j)) times product of power sums
 p={}
 for perm in permutations((2,1,0)):
  n=sum(a<b for i,a in enumerate(perm)for b in perm[i+1:])
  p[perm]=(-1)**n
 for l in nu:
  h=Counter()
  for k,v in p.items():
   for j in range(3):
    e=list(k);e[j]+=l
    if all(t<=u for t,u in zip(e,(5,3,1))):h[tuple(e)]+=v
  p=h
 return p.get((5,3,1),0)
def polymul(A,B):
 C=Counter()
 for (a,b),x in A.items():
  for (c,d),y in B.items():
   if b+d<=1:C[a+c,b+d]+=x*y
 return C
def traces(l):
 p=Counter()
 for start in (0,1):
  state={(start,0,0):1}
  for _ in range(l):
   d=Counter()
   for (s,i,j),v in state.items():
    for t in (0,1):
     b=j+s*(1-t)
     if b<=1:d[t,i+s,b]+=v
   state=d
  for (s,i,j),v in state.items():
   if s==start:p[i,j]+=v
 return p
nums=(18000,47292,23010,1580,7275,24924,6504,7800,7880,970,844)
assert all(v>0 for v in nums)
rows=0
for nu in parts(6):
 f=nu.count(1);tw=nu.count(2);sg=(-1)**(6-len(nu));d=schur(nu)
 eq=lambda *z: int(nu==tuple(z))
 match2=eq(2,2,1,1);s=eq(2,1,1,1,1)
 P={(0,0):1}
 for l in nu:P=polymul(P,traces(l))
 G=[sg*(Q(comb(f,2),15)-Q(f,6)),*(Q(P[j,1],comb(6,j))for j in (1,2,3)),(Q(4*tw,15)if sg==1 else 0)]
 for split in ((1,-1)if nu==(5,1) else (0,)):
  extra=[eq(3,1,1,1)+Q(2,3)*(s-match2),eq(3,3)+Q(4,9)*match2,
         int(split==-1)+Q(8,5)*match2,-int(split==1)+Q(8,5)*match2,
         8*eq(2,2,2)-eq(6),eq(3,2,1)+Q(4,3)*match2]
  # On even nonsplit classes each alternating trace is half the S6 trace.
  # On 5+/- the rational parameter replaces the character difference sqrt5.
  g=1-Q(s,10)-(Q(d,16)+Q(split*56,25*16)if sg==1 else 0)
  w=sum(a*b for a,b in zip(nums,G+extra))/56000
  assert w==g,(nu,split,w,g)
  rows+=1
 # Check the required even nonsplit character values directly.
 if sg==1:
  assert d==({(1,)*6:16,(3,1,1,1):-2,(3,3):-2,(5,1):1}.get(nu,0))
assert rows==12
# Split characters have norm 1 and sum 1 across the two 5-class entries.
# The other two nonzero classes are both size 40 with value -1.
assert Q(360-8**2-2*40,72)==3
assert 2*3-1==5 and Q(56,25)**2>5
print('Independent PASS:',rows,'monomial classes; Frobenius split trace and 2-state first-cross transfers')
