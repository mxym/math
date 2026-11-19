"""Dependency-free exhaustive finite sanity checks; no finite test proves the asymptotic theorems."""
from itertools import combinations,permutations
from math import comb,factorial
def need(ok,msg):
 if not ok:raise ArithmeticError(msg)
def check(n):
 V=range(n);E=list(combinations(V,2));m=len(E);M=1<<m;ix={e:1<<j for j,e in enumerate(E)}
 def edge(u,v):return ix[tuple(sorted((u,v)))]
 inc=[sum(edge(v,u) for u in V if v!=u)for v in V]
 C=[0]*M
 for l in range(3,n+1):
  for U in combinations(V,l):
   a=U[0]
   for p in permutations(U[1:]):
    if p[0]>p[-1]:continue
    Q=(a,)+p+(a,);h=sum(edge(u,v)for u,v in zip(Q,Q[1:]));C[h]+=1
 for b in ix.values():
  for mask in range(M):
   if mask&b:C[mask]+=C[mask^b]
 def con(A,bad):
  live=(1<<n)-1-bad;s=live&(-live);reach=0
  while s!=reach:
   reach=s;ss=s
   while ss:
    v=ss&(-ss);s|=A[v.bit_length()-1]&live;ss-=v
  return s==live
 nonsep=[0]*M;three=[0]*M;path_checks=triples=minimum=0
 triple=[tuple(1<<i for i in inds)for inds in combinations(range(m),3)if len({v for i in inds for v in E[i]})==6]
 for mask in range(M):
  deg=[(x&mask).bit_count() for x in inc]
  if min(deg)<2:continue
  A=[0]*n
  for i,(u,v) in enumerate(E):
   if mask>>i&1:A[u]|=1<<v;A[v]|=1<<u
  if not all(con(A,1<<i) for i in V):continue
  nonsep[mask]=1;rank=mask.bit_count()-n+1
  need(C[mask]>=comb(rank+1,2),'rank bound')
  for u,v in E:
   b=edge(u,v);p=1+C[mask]-C[mask^b] if mask&b else C[mask|b]-C[mask]
   need(p>=rank+1,'2-connected between-pair path count')
   path_checks+=1
  if n<4 or min(deg)<3 or not all(con(A,(1<<i)|(1<<j)) for i,j in E):continue
  three[mask]=1
  for a,b,c in triple:
   if mask&(a|b|c):continue
   ups=C[mask|a|b|c]-C[mask|a|b]-C[mask|a|c]-C[mask|b|c]+C[mask|a]+C[mask|b]+C[mask|c]-C[mask]
   need(ups>=1,'positive triple mixed difference');triples+=1
  if not any(three[mask^b] for b in ix.values() if mask&b):
   minimum+=1;need(sum(x==3 for x in deg)*5>=2*n,'minimal degree-three count')
  # C(K) on the extremal complete graphs is also above the degree-only path lower used.
 print('order',n,'2-connected',sum(nonsep),'3-connected',sum(three),'endpoint paths',path_checks,'disjoint extra triples',triples,'minimal-3',minimum)
for n in range(3,7):check(n)
print('finite checks passed; the high-degree/large-order conclusion follows from the mathematical proof, not this enumeration')
