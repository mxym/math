#!/usr/bin/env python3
"""Independent KK/colex and rank-nine valley verification. Standard library, no imports from the authors."""
from itertools import combinations,combinations_with_replacement
from functools import lru_cache
from math import comb
def ck(n,k):return comb(n,k) if 0<=k<=n else 0
def need(x,msg):
 if not x:raise ValueError(msg)
def fvec(p):
 f=[1]
 for a in p:f=[x+y for x,y in zip(f+[0],[0]+[a*b for b in f])]
 return f+[0]*10
mp={p for k in range(1,10)for p in combinations_with_replacement(range(1,10),k)if sum(p)==9};ind=[(fvec(p)[2]+fvec(p)[3]-fvec(p)[4],p) for p in mp]
need(len(mp)==30 and max(ind)==(54,(3,3,3)),'signed objective')
# Explicit colex initial segments, not the canonical binomial expansion.
trip=sorted(combinations(range(8),3),key=lambda s:sum(1<<x for x in s))
sh=[];completion=[]
for t in range(30):
 fam=set(trip[:t]);sh.append(len({e for S in fam for e in combinations(S,2)}))
 completion.append(sum(all(T in fam for T in combinations(Q,3))for Q in combinations(range(8),4)))
# Sorted lists of the ACTUAL nine singleton degrees (the paper drops unconstrained slots).
# Keep only potentially relevant (cost,gain,subset sizes) signatures.
V={};D1=[2-ck(d,2)+ck(d,3)for d in range(10)];B1=[ck(d,4)-ck(d,3)for d in range(10)]
for ds in combinations_with_replacement(range(8),9):
 cost=sum(D1[d]for d in ds);gain=sum(B1[d]for d in ds)
 if cost<=29:
  key=(cost,*(sum(d>=j for d in ds)for j in range(3,7)))
  V[key]=max(V.get(key,-1000),gain)
profiles=list(V.items())
@lru_cache(None)
def vert(b,ex):
 # Every high-common-neighbor edge needs both endpoints in the corresponding nested set.
 return max((g for (l,*vs),g in profiles if l<=b and all(ck(v,2)>=x for v,x in zip(vs,ex))),default=-1000)
def part(t,m=5):
 if t==0:yield ()
 for i in range(1,min(m,t)+1):
  for rem in part(t-i,i):yield (i,)+rem
d2=[1-d+ck(d,2)for d in range(10)];b2=[ck(d,3)-ck(d,2)for d in range(10)]
tab=[-1000]*30;nt=ok=0
for l3 in range(30):
 for p in part(l3):
  th=[sum(d>=j for d in p)for j in range(2,6)]
  gu=sum(ck(d,2)-d for d in p)+completion[l3]
  for e6 in range((29-l3)//10+1):
   for e5 in range((29-l3-10*e6)//6+1):
    for e4 in range((29-l3-10*e6-6*e5)//3+1):
     for e3 in range(30-l3-10*e6-6*e5-3*e4):
      nt+=1;e=(e3,e4,e5,e6);ta=tuple(sum(e[j:])for j in range(4))
      if any(ta[i]<sh[th[i+1]]for i in range(3)):continue
      e2=max(0,sh[th[0]]-ta[0])
      B=29-l3-sum(d2[j]*v for j,v in enumerate(e,3))
      v=vert(B,ta)
      if v<=-1000:continue
      ok+=1;x=gu+v-e2+sum(b2[j]*u for j,u in enumerate(e,3))
      tab[l3]=max(tab[l3],x)
need(nt==107010 and max(tab)<=0,'valley')
print('SHADOW',sh,completion);print('LOCAL',nt,ok,tab)
# 19-vertex witness, core and exterior generating polynomials independently:
W=[ck(10,j)-ck(8,j-2)+9*ck(3,j-1)+27*(j in (2,3))+27*(j==3)for j in range(20)]
need(W==[1,19,98,193,191,196,140,64,17,2]+[0]*10,'witness')
print('WITNESS',W[:10]);print('PASS independent rank-nine local exclusion')
