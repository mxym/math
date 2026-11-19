#!/usr/bin/env python3
"""Exact finite consistency checks; the unrestricted continuous claims require the proof."""
from fractions import Fraction as Q
from functools import cache
from math import comb,gcd
from collections import Counter
C=Counter()
def ck(ok,name):
    if not ok: raise RuntimeError(name)
    C[name]+=1
@cache
def tail(n,k,x):
    h,d=x.numerator,x.denominator
    return Q(sum(comb(n,j)*h**j*(d-h)**(n-j) for j in range(k,n+1)),d**n)
def primitive(a,b,x):
    # Indep. integration of the normalized integer shape beta pdf.
    return a*comb(a+b-1,b-1)*sum((-1)**j*comb(b-1,j)*x**(a+j)/(a+j) for j in range(b))
for h in range(1,9):
 for l in range(1,9):
  if gcd(h,l)!=1:continue
  m=Q(h,h+l)
  old={}
  for z in range(1,10):
   a,b=h*z,l*z
   for x in {Q(1,2),m}:
    u=tail(a+b-1,a,x)
    ck(primitive(a,b,x)==u,'beta antiderivative vs binomial')
    if x in old:
      delta=u-old[x]
      sig=(h>l)-(l>h)
      if x!=m:sig=-sig
      ck(((delta>0)-(delta<0))==sig,'two landmark increments')
    old[x]=u
for r in [Q(i,13) for i in range(1,7)]:
 for scale in [Q(i,5) for i in range(1,24)]:
  for L in [r*i/10 for i in range(1,10)]:
   q=1-r
   if scale*L>=q:continue
   ck(scale**2*(r-L)*(q+L)-(r+scale*L)*(q-scale*L)==(scale**2-1)*r*q-(q-r)*(scale**2+scale)*L,'paired level factor')
for b in range(2,11):
 for k in range(1,17):
  for e in (0,1):
   for p in (Q(0),Q(1,3*b),Q(1,2*b),Q(1,b)):
    ck(tail(b*k-1+e,k,p)<=tail(b-1+e,1,p),'integer endpoints and interior')
for b0 in range(2,9):
 for d in range(1,18):
  for h in range(1,d+1):
   if gcd(h,d)!=1:continue
   t=Q(h,d)
   if t<Q(1,b0):continue
   for p in (Q(0),Q(1,2*b0),Q(1,b0)):
    for k in range(1,19):
     ck(tail(k*d//h,k,p)<=1-(1-p)**(d//h),'floored betting law')
# Half-integer shapes: I_x(a,b)=I_x(1/2,1/2)+sqrt(x(1-x))/pi*R,
# so with x fixed signs of differences are the signs of exact rational R's.
def half_offset(h,l,x,back=False):
    a=b=Q(1,2); nrm=Q(1); c=Q(0)  # nrm=B(a,b)/pi starts at 1
    for axis in ('ba' if back else 'ab'):
     for j in range(((h if axis=='a' else l)-1)//2):
      v=x**int(a-Q(1,2))*(1-x)**int(b-Q(1,2))/nrm
      if axis=='a':
       c-=v/a; nrm*=a/(a+b); a+=1
      else:
       c+=v/b; nrm*=b/(a+b); b+=1
    return c
for h in range(1,10,2):
 for l in range(1,10,2):
  if gcd(h,l)!=1:continue
  m=Q(h,h+l);old={}
  for z in range(1,10,2):
   for x in {Q(1,2),m}:
    v=half_offset(z*h,z*l,x)
    ck(v==half_offset(z*h,z*l,x,True),'half-integer recurrence path independence')
    if x in old:
     sig=(h>l)-(l>h)
     if x!=m:sig=-sig
     ck(((v>old[x])-(v<old[x]))==sig,'two half-integer landmark increments')
    old[x]=v
for key,val in C.items():print('PASS',key,':',val)
