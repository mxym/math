#!/usr/bin/env python3
from itertools import product,combinations
from math import prod
from collections import Counter
import sys
class P(dict):
 def __init__(self,x=0):
  super().__init__(x if isinstance(x,dict) else {(0,0,0,0): x} if x else {})
 def __add__(self,x):
  z=Counter(self);z.update(P(x));return P({k:v for k,v in z.items() if v})
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.items()})
 def __sub__(self,x):return self+-P(x)
 def __rsub__(self,x):return P(x)+-self
 def __mul__(self,x):
  z=Counter()
  for a,b in self.items():
   for c,d in P(x).items():
    z[tuple(i+j for i,j in zip(a,c))]+=b*d
  return P({k:v for k,v in z.items() if v})
 __rmul__=__mul__
 def __pow__(self,k):
  if not isinstance(k,int) or k<0:raise ValueError('bad exponent')
  return prod([self]*k,start=P(1))
 def val(self,*x):return sum(a*prod(y**p for y,p in zip(x,k)) for k,a in self.items())
def need(x,why):
 if not x:raise ArithmeticError(why)
def gap2(a,h,t):
 # work throughout with Z2=2z; W2=2W, so no rational coefficients needed
 r=sum(h);Z2=t*(t+1)
 W2=a*(a-1)+2*a*r+2*sum(x*y for x,y in combinations(h,2))-3*Z2
 return W2*(a+sum(x*x for x in h)-1-Z2)-a*(a-1+r)**2-sum((x*(a+r-x)-Z2)**2 for x in h)
basis=[P({tuple(int(r==s) for r in range(4)):1}) for s in range(4)]
u,i,j,k=basis;t=u+1;y=[i+j+k,j+k,k];h=[t+1+x for x in y];a=t+2+sum(y)
G=gap2(a,h,t)
need(len(G)==70 and min(G.values())==2 and max(G.values())==516 and G.get((0,0,0,0))==96,'identity support/lower/constant')
def explicit(a,h,B):
 T=a*(a-1)+2*a*sum(h)+2*sum(B)
 D=a*(a-1+sum(h))**2+sum((a*h[l]+sum(B[k] for k,ij in enumerate(combinations(range(3),2)) if l in ij))**2 for l in range(3))
 # Directly compute the minimum of twice the signed edge sum, not the rounded formula
 V=min(x*x-a+2*x*sum(g*v for g,v in zip(h,s))+2*sum(e*s[l]*s[m] for e,(l,m) in zip(B,combinations(range(3),2))) for x in range(-a,a+1,2) for s in product((-1,1),repeat=3))
 return -T*V-D
for args in product(range(4),repeat=4):
 u,i,j,k=args;t=u+1;y=[i+j+k,j+k,k];h=[t+1+x for x in y];a=t+2+sum(y);B=[x*y-t*(t+1)//2 for x,y in combinations(h,2)]
 need(G.val(*args)==gap2(a,h,t)==explicit(a,h,B),'raw cuts vs polynomial')
print('positive coefficient count',len(G),'min',min(G.values()),'max',max(G.values()),'constant',G[(0,0,0,0)])
print('verified direct signed-count cut computations in 256 integer parameter instances; PASS')
