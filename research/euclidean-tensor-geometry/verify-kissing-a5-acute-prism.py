#!/usr/bin/env python3
"""Rational reverse-convex prism certificate for the two acute A5 holes."""
from fractions import Fraction as F
from itertools import combinations,product
from math import isqrt
if not __debug__:raise RuntimeError("enable assertions")
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def val(z):return dot(z[:6],z[:6])/2+z[6]**2/4
def interp(a,b,t):return tuple(x+(y-x)*t for x,y in zip(a,b))
def rt(q,n):
 assert q>=0
 a=isqrt(q.numerator);b=isqrt(q.denominator)
 if a*a==q.numerator and b*b==q.denominator:return F(a,b),F(a,b)
 S=2**n;i=isqrt(q.numerator*S*S//q.denominator)
 return F(i,S),F(i+1,S)
def verify(n):
 P=[]
 for k in range(6):
  a=[0]*(5-k)+[1]*k;w=[1+a[1],0,a[0],a[4],a[3],a[2]];mu=F(sum(w),6)
  for h in [0,1]:P.append(tuple(x-mu for x in w)+(F(h),F(k==4)))
 H=[(p,p)for p in P if val(p)>=1];edgecount=0
 for i,j in combinations(range(12),2):
  if i//2!=j//2 and i%2!=j%2:continue
  edgecount+=1;a,b=P[i],P[j];v=tuple(y-x for x,y in zip(a,b))
  A=val(v);B=val(b)-val(a)-A;C=val(a)-1;D=B*B-4*A*C
  if D<0:continue
  l,u=rt(D,n)
  for s,t in [(-u,-l),(l,u)]:
   s=(s-B)/(2*A);t=(t-B)/(2*A)
   if t<=0 or s>=1:continue
   if s==t==0 or s==t==1:continue
   assert 0<s<=t<1
   H.append((interp(a,b,s),interp(a,b,t)))
 assert edgecount==36 and len(H)==16
 pi=(0,2,1,5,4,3)
 def slack(z,w):
  return dot(z[:6],tuple(w[i]for i in pi))/2+z[6]*w[6]/4-F(1,2)-z[7]*w[7]/2
 assert min(slack(v,w)for p,q in product(H,repeat=2)for v,w in product(p,q))==0
 print('bits',n,'prism edges',edgecount,'generators',len(H),'bilinear lower bounds passed')
for n in (48,77):verify(n)
