#!/usr/bin/env python3
"""Independent check of Marcus distinct-support reduction and length-twelve routing."""
from functools import lru_cache
from itertools import combinations,permutations
from math import prod
def ok(x):
 if not x:raise ValueError('independent check failed')
def cycles():
 for n in range(5,9):
  ed=[{i,(i+1)%n}for i in range(n)];short=alt=0
  for order in permutations(range(n)):
   pos={x:i for i,x in enumerate(order)}
   p=next((i for i in range(n)if (pos[i]-pos[(i-1)%n])*(pos[i]-pos[(i+1)%n])<0),None)
   if p is None:
    alt+=1;ok(n%2==0);continue
   short+=1;a,b=tuple(ed[p]);new=[]
   for q in order:
    if q==p:continue
    h={b if x==a else a if x==b else x for x in ed[q]}if pos[q]>pos[p]else ed[q]
    new.append(h)
   vs=set.union(*new);ok(len(vs)==n-1 and len({tuple(sorted(x))for x in new})==n-1)
   ok(all(sum(v in h for h in new)==2 for v in vs))
   live={next(iter(vs))}
   for _ in range(n):live|=set().union(*(h for h in new if h&live))
   ok(live==vs)
  print('CYCLE',n,short,alt)
def routing(m=6):
 n=2*m;A=[(2*i,2*i+1)for i in range(m)];B=[(2*i+1,(2*i+2)%n)for i in range(m)]
 gates=A+B;c,s,q=5,12,13
 # U(row,col) is built by actual chronological column propagation.
 U=[]
 for j in range(n):
  u=[int(j==i)for i in range(n)]
  for layer in (A,B):
   v=[0]*n
   for a,b in layer:v[a]=c*u[a]+s*u[b];v[b]=-s*u[a]+c*u[b]
   u=v
  U.append(u)
 @lru_cache(None)
 def minor(I,J):
  if not J:return 1
  y=J&-J;j=y.bit_length()-1;ans=0
  for i,z in enumerate(U[j]):
   if z and I>>i&1:ans+=(-1 if (I% (1<<i)).bit_count()%2 else 1)*z*minor(I^(1<<i),J^y)
  return ans
 def perm_occupied(pair,mask,b):
  a,z=pair
  return mask^((1<<a)|(1<<z))if b and ((mask>>a)^(mask>>z))&1 else mask
 def ends(Z,word):
  x=y=Z
  for i,pa in enumerate(A):x=perm_occupied(pa,x,word>>i&1)
  for i,pa in enumerate(B,m):y=perm_occupied(pa,y,word>>i&1)
  return y,x
 Z=sum(1<<x for x in range(0,n,2))
 for w in range(1<<n):
  I,J=ends(Z,w);h=w.bit_count();k=n-h
  amp=minor(I,J)
  ok(amp**2==c**(2*k)*s**(2*h)+s**(2*k)*c**(2*h)+2*(-1)**(m-1+h)*(c*s)**n)
 # All pairs of omitted switches and every assignment to the remaining ten.
 # Find the suitable occupancy by a direct enumeration rather than cycle toggling.
 by={}
 for z in range(1<<n):
  inactive=tuple(i for i,(a,b)in enumerate(gates)if ((z>>a)^(z>>b))&1==0)
  if len(inactive)==2:by.setdefault(inactive,z)
 ok(len(by)==n*(n-1)//2)
 num=0
 for (a,b),z in by.items():
  k=z.bit_count();free=[i for i in range(n)if i not in(a,b)]
  for t in range(1<<(n-2)):
   w=sum(1<<bit for j,bit in enumerate(free)if t>>j&1);I,J=ends(z,w);h=t.bit_count()
   ok(minor(I,J)**2*q**(2*(n-2))==q**(4*k)*c**(2*(n-2-h))*s**(2*h));num+=1
 print('ROUTING',n,1<<n,num)
def positive():
 # Two triangles linked at an articulation and two bridges. Grouped blocks
 # can be applied in ANY order; at each final set the intermediate path is unique.
 n=7;blocks=({0,1,2},{2,3,4},{1,5},{4,6})
 for order in permutations(blocks):
  for J in range(1<<n):
   a={J}
   for block in order:
    M=sum(1<<i for i in block);nxt=[]
    for S in a:
     k=(S&M).bit_count()
     nxt.extend((S&~M)|sum(1<<i for i in t)for t in combinations(sorted(block),k))
    ok(len(nxt)==len(set(nxt)));a=set(nxt)
 print('FOREST block orders 24, starting masks 128')
if __name__=='__main__':
 cycles();routing();positive();print('PASS independent')
