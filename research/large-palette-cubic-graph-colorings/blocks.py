"""Unlabelled open-ear enumeration for 2-connected subcubic supports of the low-degree log-chromatic expansion; exact arithmetic."""
from itertools import combinations,permutations,product
from collections import Counter,defaultdict
from functools import lru_cache
from math import factorial,prod
from fractions import Fraction as Q
import sys
K=int(sys.argv[1]) if len(sys.argv)>1 else 7
V=K+1
def maskgraph(n,edges):
 a=[0]*n
 for u,v in edges:a[u]|=1<<v;a[v]|=1<<u
 return tuple(a)
def edges(a):
 return [(u,v) for u in range(len(a)) for v in range(u) if a[u]>>v&1]
def cycle(n):return maskgraph(n,[(i,(i+1)%n) for i in range(n)])
def bic(a):
 if len(a)<3 or min(x.bit_count() for x in a)<2:return False
 U=(1<<len(a))-1
 for i in range(len(a)):
  allow=U^(1<<i); seen=0; fr=allow&-allow
  while fr:
   y=fr&-fr;seen|=y;fr=(fr|a[y.bit_length()-1])&allow&~seen
  if seen!=allow:return False
 return True
@lru_cache(32768)
def canon(a):
 n=len(a)
 if max(x.bit_count() for x in a)==2:return (n,'C'),2*n
 c=[x.bit_count() for x in a]
 while True:
  keys=[(c[i],tuple(sorted(c[j] for j in range(n) if a[i]>>j&1))) for i in range(n)]
  ix={key:i for i,key in enumerate(sorted(set(keys)))}; cc=[ix[key] for key in keys]
  if len(set(cc))==len(set(c)):break
  c=cc
 groups=[tuple(j for j in range(n) if cc[j]==t) for t in sorted(set(cc))]
 best=None;aut=0
 for g in product(*(permutations(t) for t in groups)):
  p=sum(g,()); bits=0
  for i in range(n):
   for j in range(i):bits=bits*2+((a[p[i]]>>p[j])&1)
  if best is None or bits<best:best=bits;aut=1
  elif bits==best:aut+=1
 return (n,best),aut

def hascycle(a,k):
 n=len(a)
 def walk(v,u,seen,d):
  if d==k:return bool(a[u]>>v&1)
  rest=a[u]&~seen&~((1<<v)-1)
  while rest:
   bit=rest&-rest; rest^=bit
   if walk(v,bit.bit_length()-1,seen|bit,d+1):return True
  return False
 return any(walk(v,v,1<<v,1) for v in range(n))
def gen(kind):
 bad=3 if kind=='P' else 4
 allf={};stack=[cycle(v) for v in range(3,V+1) if v!=bad]
 while stack:
  a=stack.pop(); key,aut=canon(a)
  if key in allf:continue
  if hascycle(a,bad):continue
  allf[key]=(a,aut)
  n=len(a);low=[v for v in range(n) if a[v].bit_count()==2];old=edges(a)
  for x,y in combinations(low,2):
   for j in range(V-n+1):
    if j==0 and a[x]>>y&1:continue
    path=[x,*range(n,n+j),y]
    stack.append(maskgraph(n+j,old+list(zip(path,path[1:]))))
 return allf

def subgraph_data(a):
 """IE chromatic polynomial normalized + proper biconnected subgraph counts (ignoring isolated vertices)."""
 E=edges(a);n=len(a);m=len(E);p=[0]*(K+1);subs=Counter()
 for b in range(1<<m):
  par=list(range(n));r=0;et=[];verts=set()
  def root(x):
   while par[x]!=x:x=par[x]
   return x
  for j,(x,y) in enumerate(E):
   if b>>j&1:
    et.append((x,y));verts.add(x);verts.add(y);s,t=root(x),root(y)
    if s!=t:r+=1;par[s]=t
  if r<=K:p[r]+=(-1)**len(et)
  if b==(1<<m)-1 or len(verts)<3 or len(et)<len(verts):continue
  lab={x:j for j,x in enumerate(sorted(verts))}
  c=maskgraph(len(verts),[(lab[x],lab[y]) for x,y in et])
  if bic(c):subs[canon(c)[0]]+=1
 return p,subs
def sweight(a):
 """Bound inj(F,G)/|G| from best spanning-tree embedding, fixing one leaf first."""
 E=edges(a);n=len(a);best=3*2**(n-2)
 for T in combinations(E,n-1):
  tr=maskgraph(n,T);seen=1;last=0
  while last!=seen:
   last=seen;seen|=sum(1<<x for x in range(n) if tr[x]&last)
  if seen==(1<<n)-1:
   N=sum(1 for x in tr if x.bit_count()>=2)
   best=min(best,3*2**N)
 return best
if __name__ == '__main__':
 for kind in 'PH':
  allf=gen(kind); print(kind,'number of blocks',len(allf),flush=True)
  weights={}; bounds=[Q(0)]*(K+1); types=Counter()
  for key,(a,aut) in sorted(allf.items(),key=lambda v:len(edges(v[1][0]))):
   n=len(a);m=len(edges(a));p,subs=subgraph_data(a);d=[Q(0)]*(K+1)
   for k in range(1,K+1):
    d[k]=Q(k*p[k]-sum(j*d[j]*p[k-j] for j in range(1,k)),k)
   for k in range(1,K+1):
    d[k]+=Q(m,k)
    d[k]-=sum(v*weights[h][k] for h,v in subs.items())
   assert all(x==0 for x in d[:n-1]); assert d[n-1]==(-1)**m,(key,n,m,d,subs)
   weights[key]=d ;types[n,m]+=1
   lim=Q(sweight(a),aut)
   for k in range(1,K+1):bounds[k]+=abs(d[k])*lim
   if n<=6: print('block',n,m,'aut',aut,'w',','.join(str(x) for x in d[1:]))
  print('type counts',sorted(types.items()))
  print('per-vertex abs contribution bounds',bounds)
