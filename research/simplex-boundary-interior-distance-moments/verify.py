"""Exact finite cone certificate for barycentric simplex directional stop-loss."""
from itertools import combinations,product
from functools import lru_cache
from math import gcd
from collections import Counter
import sys
def need(b,m):
 if not b: raise ArithmeticError(m)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def det(A):
 if not A:return 1
 return sum((-1)**j*x*det([r[:j]+r[j+1:] for r in A[1:]]) for j,x in enumerate(A[0]) if x)
def cross(A):
 return tuple((-1)**j*det([r[:j]+r[j+1:] for r in A]) for j in range(len(A)+1))
def norm(r):
 g=gcd(*r);return tuple(i//g for i in r) if g else None
def make(d):
 D=d+1; I=tuple(tuple(int(i==j) for i in range(D)) for j in range(D))
 pairs=list(combinations(range(D),2))
 forms=[tuple(int(i<=l<j) for l in range(d))+(0,) for i,j in pairs]
 shifted=[f[:-1]+(-1,) for f in forms]
 roots=I+tuple(shifted); allr=set()
 for group in combinations(roots,d):
  v=norm(cross(group));
  if not v:continue
  for t in (v,tuple(-k for k in v)):
   if min(t)>=0:allr.add(t)
 def rank(V):
  if len(V)==0:return 0
  if len(V)==1:return 1
  for k in range(min(len(V),D),1,-1):
   if any(det([tuple(r[j] for j in J) for r in rows]) for rows in combinations(V,k) for J in combinations(range(D),k)):return k
  return 1
 @lru_cache(None)
 def tri(R):
  k=rank(R)
  if len(R)==k:return (R,)
  facets={tuple(r for r in R if dot(f,r)==0) for f in roots if dot(f,R[0])!=0}
  faces=[F for F in sorted(facets) if rank(F)==k-1]
  need(faces,'empty face list')
  return tuple((R[0],)+simp for f in faces for simp in tri(f))
 for mask in product((0,1),repeat=len(pairs)):
  R=tuple(sorted(v for v in allr if all(dot(f,v)*(2*b-1)>=0 for f,b in zip(shifted,mask))))
  if rank(R)<D or not any(mask):continue
  for basis in tri(R):
   need(len(basis)==D and det(basis)!=0,'degenerate cone')
   yield pairs,forms,mask,basis
def certificate(d,R,pairs,F,mask):
 D=len(R); unit=[16**i for i in range(D)]; total=Counter();X=[[sum(r[:i]) for r in R] for i in range(D)];da=tuple(r[0] for r in R); Ft=[tuple(dot(f,r) for r in R) for f in F]
 def mul(P,L):
  out=Counter()
  for k,v in P.items():
   for m,c in zip(unit,L):
    if c:out[k+m]+=c*v
  return out
 for l,(i,j) in enumerate(pairs):
  if not mask[l]:continue
  w=tuple(k-r[-1] for k,r in zip(Ft[l],R))
  need(min(w)>=0,'invalid sign')
  p=Counter({0:(-1)**(d-1+i+j)})
  for k,(u,v) in enumerate(pairs):
   for _ in range(2-int(i in (u,v))-int(j in (u,v))):p=mul(p,Ft[k])
  for _ in range(2*d-1):p=mul(p,w)
  T=mul(mul(p,[2*x-a for x,a in zip(X[i],da)]),[2*x-a for x,a in zip(X[j],da)])
  Q=mul(mul(p,w),w)
  for k,v in T.items():total[k]+=(2*d+1)*v
  for k,v in Q.items():total[k]+=2*d*v
 return total
def main():
 for d in (2,3):
  stats=Counter(); bad=0
  for pairs,F,mask,basis in make(d):
   co=certificate(d,basis,pairs,F,mask)
   if min(co.values())<0:
    bad+=1
    if bad<8: print('bad',d,basis,min(co.values()),sum(v<0 for v in co.values()),flush=True)
   stats['cones']+=1;stats['positive coeffs']+=sum(v>0 for v in co.values());stats['zeros']+=sum(v==0 for v in co.values())
  expected={2:(4,74,10),3:(15,4464,825)}[d]
  need(bad==0 and (stats['cones'],stats['positive coeffs'],stats['zeros'])==expected, 'failed cone/coefficient checks')
  print(d,stats,'failed',bad,flush=True)
if __name__=='__main__':main()
