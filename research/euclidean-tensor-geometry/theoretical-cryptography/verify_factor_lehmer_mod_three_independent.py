#!/usr/bin/env python3
"""Separate low-degree audit of the global mod-three minimum at 431/250.
No Schur tests, root finding, floating point, exterior powers, or height cutoff."""
import sys
from fractions import Fraction as Q
from math import comb,gcd
from functools import lru_cache
R=Q(431,250)
def polyrem(a,b):
 a=list(a)
 while len(a)>=len(b):
  m=len(a)-len(b);x=a.pop()
  for i in range(len(b)-1):a[m+i]-=x*b[i]
 return tuple(a)
@lru_cache(None)
def phi(n):
 p=[-1]+[0]*(n-1)+[1]
 for i in range(1,n):
  if n%i:continue
  f=phi(i);out=[0]*(len(p)-len(f)+1)
  for j in range(len(out)-1,-1,-1):
   c=p[j+len(f)-1];out[j]=c
   for k,t in enumerate(f):p[j+k]-=c*t
  assert not any(p);p=out
 return tuple(p)
def hascycl(p):
 d=len(p)-1
 return any(not any(polyrem(p,f))for f in [phi(i)for i in range(1,2*d*d+1)]if len(f)<=d+1)
def sq(a):
 # F(x)F(-x) up to sign is monic in x^2 and has squared roots.
 n=len(a)-1;b=[0]*(n+1)
 for i,z in enumerate(a):
  for j,t in enumerate(a):
   if (i+j)%2==0:b[(i+j)//2]+=(-1)**((n+j)%2)*z*t
 assert b[-1]==1
 return b
def go(d):
 m=d//2;B=[int(d-2+R**j+R**-j)for j in range(m+1)]
 seen=cycl=0;hist={};rest=[]
 def dfs(a,p):
  nonlocal seen,cycl
  k=len(a)
  if k==m+1:
   A=a+a[-2::-1];seen+=1
   if hascycl(A):cycl+=1;return
   r=R
   for t in range(10):
    if any(abs(x)*r.denominator>comb(d,j)*r.numerator for j,x in enumerate(A)):
     hist[t]=hist.get(t,0)+1;return
    A=sq(A);r*=r
   rest.append(a);return
  c=sum(a[i]*p[k-i]for i in range(1,k))
  for sk in range(-B[k],B[k]+1):
   if (sk+c)%k:continue
   z=-(sk+c)//k
   if z%3==2:dfs(a+[z],p+[sk])
 dfs([1],[d]);print('independent',d,seen,cycl,hist,'survivors',rest,flush=True)
 assert rest==([[1,-1,-1]]if d==4 else [])
if __name__=='__main__':
 for d in [2,4,6,8,10]:go(d)
