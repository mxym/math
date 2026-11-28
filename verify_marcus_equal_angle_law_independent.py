#!/usr/bin/env python3
"""Independent full-law test in the feasible equal-angle region, not just necessary observations."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb
def trial(m,c,s,den):
 n=2*m;A=[(2*i,2*i+1)for i in range(m)];B=[(2*i+1,(2*i+2)%n)for i in range(m)];g=A+B
 x=F(s*s,c*c);K=F((c*s)**n,den**(2*n));D=(-1)**(m-1)*K;tau=(x**-2-1)/2
 assert x>=1 and c*c+s*s==den*den
 prob=[]
 for b in range(1<<n):
  k=b.bit_count()-m
  q=K*(x**k-(-1 if k%2 else 1)*(1-tau*k))
  assert q>=0;prob.append(q)
 assert sum(prob)==1
 # Direct gate-by-gate construction of the U columns, numerator denominator den^2.
 U=[]
 for j in range(n):
  u=[int(i==j)for i in range(n)]
  for layer in(A,B):
   v=[0]*n
   for a,b in layer:v[a]=c*u[a]+s*u[b];v[b]=-s*u[a]+c*u[b]
   u=v
  U.append(u)
 @lru_cache(None)
 def minor(I,J):
  if not J:return 1
  y=J&-J;j=y.bit_length()-1
  return sum((-1 if (I%(1<<i)).bit_count()%2 else 1)*z*minor(I^(1<<i),J^y)for i,z in enumerate(U[j])if z and I>>i&1)
 checks=0
 for J in range(1<<n):
  mass={}
  for b,q in enumerate(prob):
   y=J
   for i,(u,v)in enumerate(g):
    if b>>i&1 and ((y>>u)^(y>>v))&1:y^=(1<<u)|(1<<v)
   mass[y]=mass.get(y,0)+q
  for I in range(1<<n):
   if I.bit_count()!=J.bit_count():continue
   if F(minor(I,J)**2,den**(4*I.bit_count()))!=mass.get(I,0):raise ArithmeticError('wrong common law')
   checks+=1
 assert checks==comb(2*n,n);print('PASS all input/output minor equations',m,c,s,checks)
if __name__=='__main__':
 trial(3,3,4,5);trial(4,3,4,5);trial(5,20,21,29)
