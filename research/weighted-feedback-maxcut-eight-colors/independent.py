"""Independent facet-rank/weighted objective certificate, using the shared pinned input parser."""
import collections,itertools,json,math,pathlib,sys
from fractions import Fraction
from inputs import arguments,load
args=arguments()
def require(b,obj): 
 if not b: raise ValueError(obj)
def rank_mod(data,p=1009):
 piv={}
 for row in data:
  r=list(row)
  for j in range(len(r)):
   if not r[j]:continue
   if j in piv:
    f=r[j]; r=[(a-f*b)%p for a,b in zip(r,piv[j])]
   else:
    mul=pow(r[j],-1,p);piv[j]=[a*mul%p for a in r];break
 return len(piv)
for n,num,positive,low in [(5,2,1,0),(6,3,1,Fraction(5,12)),(7,11,4,Fraction(1,8)),(8,147,29,Fraction(11,32))]:
 rows=load(n,args)
 E=list(itertools.combinations(range(n),2)); require(len(rows)==num and set(rows)==set(map(str,range(1,num+1))),'row list')
 cuts=[[((mask>>i)^(mask>>j))&1 for i,j in E] for mask in range(1<<(n-1))]
 gaps={}
 for j,row in rows.items():
  require(len(row)==len(E),'columns'); vals=[sum(v*w for v,w in zip(row,c)) for c in cuts];require(max(vals)==0,'input cut inequality')
  require(rank_mod([c for c,v in zip(cuts,vals) if v==0])==len(E)-1,(n,j,'facet rank'))
  a=dict(zip(E,row))
  if 0 in row or any(a[i,j]*a[i,k]*a[j,k]<0 for i,j,k in itertools.combinations(range(n),3)):continue
  # Balanced signs on all triangles are equivalent to switching to all-positive.
  w={e:abs(x) for e,x in a.items()};mass=sum(w.values()); deg=[sum(v for e,v in w.items() if i in e) for i in range(n)]
  hist=collections.Counter([0])
  for v in deg: 
   old=hist.copy(); hist.update({t+v:k for t,k in old.items()})
  K=Fraction(sum(k*abs(2*t-2*mass) for t,k in hist.items()),1<<n)
  mc=0
  for k in range(n//2+1):
   for S in itertools.combinations(range(n),k):
    mcut=sum(deg[i] for i in S)-2*sum(w[e] for e in itertools.combinations(S,2))
    mc=max(mc,mcut)
  gap=Fraction(15*mc-6*mass-4*K,mc); require(gap>=0,(n,j,gap));gaps[j]=gap
 require(len(gaps)==positive and min(gaps.values())==low,(n,gaps))
 print(n,num,'verified facets mod 1009 + exact source; positive',len(gaps),'minimum',min(gaps.values()),'at IDs',[i for i,v in gaps.items() if v==min(gaps.values())])
