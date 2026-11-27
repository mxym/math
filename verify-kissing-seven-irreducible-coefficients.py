#!/usr/bin/env python3
"""Exact scalar and group identities for KissingSevenIrreducible.md (stdlib)."""
from fractions import Fraction as Q
from itertools import product
from math import prod
if not __debug__: raise RuntimeError("enable assertions")
def add(a,b):return [Q(x)+y for x,y in zip(a+[0]*max(0,len(b)-len(a)),b+[0]*max(0,len(a)-len(b)))]
def sc(a,s):return [s*Q(x) for x in a]
def mul(a,b):
 r=[Q(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return r
def ev(a,x):return sum(v*x**i for i,v in enumerate(a))
P=[[Q(1)],[Q(0),Q(1)]]
for k in range(1,6):P.append(sc(add(sc([0]+P[-1],2*k+5),sc(P[-2],-k)),Q(1,k+5)))
F=[Q(1)]
for root in [Q(1,2),-Q(127,200),-Q(127,200),-Q(1,10),-Q(1,10),-Q(327,100)]:F=mul(F,[-root,1])
r=F[:];A=[Q(0)]*7
for k in reversed(range(7)):
 A[k]=r[k]/P[k][-1];r=add(r,sc(P[k],-A[k]))
assert not any(r) and all(x>0 for x in A)
F=sc(F,1/A[0]);A=sc(A,1/A[0]);assert A[0]==1 and F[-1]>22
C=[(1+7*ev(p,Q(1,7)))/8 for p in P]
off=112*(1-A[4]*C[4]/16-A[6]*C[6]/144)-ev(F,1)
h=add(sc(P[4],-56*A[4]),sc(P[6],Q(56,3)*A[6]))
assert off>-94 and not any(h[1::2]) and all(a>b for a,b in zip(h[::2],[-160,2911,-5580,419]))
assert 419*14*Q(3,100)-5580>=-5405 and -160-419*7*Q(3,100)**2>=-163
# Field exponents and the Hamming radius-one partition.
field=[1]
while len(field)<7:
 t=2*field[-1];field.append(t^11 if t>=8 else t)
assert sorted(field)==list(range(1,8))
rows=[[(-1)**((a&j).bit_count()) for a in field]for j in range(8)]
ham={tuple(s*x for x in row)for row in rows for s in [-1,1]}
assert len(ham)==16 and all(sum(sum(a!=b for a,b in zip(w,h))<=1 for h in ham)==1 for w in product([-1,1],repeat=7))
assert {tuple(row[(2*i)%7]for i in range(7))for row in rows}==set(map(tuple,rows))
out={n:[(a,b,c,d)for a in range(3)for b in range(2)for c in range(5)for d in range(3)if 8*a+14*b+28*c+56*d==n]for n in range(127,133)}
assert out=={127:[],128:[(2,0,0,2),(2,0,2,1),(2,0,4,0)],129:[],130:[],131:[],132:[]}
print("PASS: scalar dual, moment relaxation, Hamming partition, normalizer and orbit counts")
