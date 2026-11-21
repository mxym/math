#!/usr/bin/env python3
"""Field irreducibility certificates for the only two residual repeated-largest/pure signatures. No CAS."""
from math import gcd
def req(x):
 if not x:raise ArithmeticError('bad certificate')
def trim(f):
 while f and f[-1]==0:f.pop()
 return f
def monic(f,p):
 return [(x*pow(f[-1],-1,p))%p for x in f] if f else []
def sub(f,g,p):return trim([((f[i] if i<len(f) else 0)-(g[i] if i<len(g) else 0))%p for i in range(max(len(f),len(g)))])
def red(f,g,p):
 while len(f)>=len(g):
  a=f[-1]*pow(g[-1],-1,p)%p
  f=sub(f,[0]*(len(f)-len(g))+[(a*t)%p for t in g],p)
 return f
def gcdp(f,g,p):
 while g:f,g=g,red(f,g,p)
 return monic(f,p)
def times(f,g,H,p):
 c=[0]*(len(f)+len(g))
 for i,a in enumerate(f):
  for j,b in enumerate(g):c[i+j]=(c[i+j]+a*b)%p
 return red(trim(c),H,p)
def power(n,H,p):
 z=[1];x=[0,1]
 while n:
  if n%2:z=times(z,x,H,p)
  x=times(x,x,H,p);n//=2
 return z
def prove(d,b,x,p):
 # (x+Y^d-x^b)^2-Y^d-x+Y
 k=x-x**b;H=[0]*(2*d+1);H[0]=(k*k-x)%p;H[1]=1;H[d]=(2*k-1)%p;H[-1]=1
 n=2*d;Y=[0,1]
 for s in range(2,n+1):
  if n%s==0 and all(s%i for i in range(2,s)):req(gcdp(H,sub(power(p**(n//s),H,p),Y,p),p)==[1])
 req(power(p**n,H,p)==Y);print('Rabin irreducibility PASS',d,b,'X',x,'mod',p,'ascending',H)
for t in [(3,5,2,3),(5,3,6,11)]:prove(*t)
