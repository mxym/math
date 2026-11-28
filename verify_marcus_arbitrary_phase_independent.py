#!/usr/bin/env python3
"""Independent all-minor verification of the U(2) ring Walsh affine space."""
from functools import lru_cache
from math import comb,prod
def g(x):return (x,0)
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return (a[0],-a[1])
def norm(a):return a[0]*a[0]+a[1]*a[1]
def trial(m,mode):
 n=2*m;h=125;A=[(2*i,2*i+1)for i in range(m)];B=[(2*i+1,(2*i+2)%n)for i in range(m)];co=A+B
 U=[];sq=[];cross=g(1)
 for j in range(n):
  c,s=[(3,4),(4,3),(5,0)if mode=='degenerate' else(3,4)][j%3]
  ph=[g(5),(3,4),(-4,3),(3,-4),(0,5)]
  r=(ph[(j*j+2)%5],ph[(2*j+2)%5]);t=(ph[(j+3)%5],ph[(j*j+1)%5])
  M=[[mul(mul(r[a],t[b]),g(((c,s),(-s,c))[a][b]))for b in range(2)]for a in range(2)]
  U.append(M);sq.append(norm(M[0][0]))
  cross=mul(cross,mul(M[0][0]if j<m else M[1][1],conj(M[1][0])))
 d=(-1)**(m-1)*cross[0];den=h**(2*n);P=[]
 for b in range(1<<n):
  q=prod(h*h-z if b>>j&1 else z for j,z in enumerate(sq))+(-1)**b.bit_count()*(d+sum((j*j+1)*(-1)**(b>>j&1)for j in range(n)))
  P.append(q)
 assert sum(P)==den
 cols=[]
 for j in range(n):
  v=[g(int(i==j))for i in range(n)]
  for layer in (range(m),range(m,n)):
   w=[g(0)]*n
   for k in layer:
    a,b=co[k];M=U[k];w[a]=add(mul(M[0][0],v[a]),mul(M[0][1],v[b]));w[b]=add(mul(M[1][0],v[a]),mul(M[1][1],v[b]))
   v=w
  cols.append(v)
 @lru_cache(None)
 def minor(I,J):
  if not J:return g(1)
  bit=J&-J;j=bit.bit_length()-1;y=g(0)
  for i,z in enumerate(cols[j]):
   if z!=g(0)and I>>i&1:
    u=mul(z,minor(I^(1<<i),J^bit))
    y=add(y,neg(u)if(I%(1<<i)).bit_count()%2 else u)
  return y
 checks=0
 for J in range(1<<n):
  mass={};k=J.bit_count()
  for w,q in enumerate(P):
   y=J
   for j,(a,b)in enumerate(co):
    if w>>j&1 and ((y>>a)^(y>>b))&1:y^=(1<<a)|(1<<b)
   mass[y]=mass.get(y,0)+q
  for I in range(1<<n):
   if I.bit_count()==k:
    assert norm(minor(I,J))*den==mass.get(I,0)*h**(4*k);checks+=1
 assert checks==comb(2*n,n);print('ALL',m,mode,checks,'complex-interference',cross[0]!=0 and cross[1]!=0,flush=True)
if __name__=='__main__':
 for m in [2,3,4]:
  for mode in ['general','degenerate']:trial(m,mode)
