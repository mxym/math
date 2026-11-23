from time import process_time
import hashlib,json
"""Rank-independent Q4 initial catalogue. Vertex numbering in C8 conflict order."""
from itertools import combinations,product,permutations
from collections import Counter
import numpy as np
V=range(8);Z=range(11)
def bits(x):return [i for i in range(x.bit_length()) if x>>i&1]
masks=[x for x in range(256)if x.bit_count()>=2 and not(x&(x<<1))and not(x&1 and x&128)]
def trans(x,s,f):
 return sum(1<<((s+(1-2*f)*h)%8)for h in bits(x))
per=[[trans(x,s,f)for x in range(256)]for s,f in product(V,range(2))]
def incidence():
 d=[0]*8;pp=Counter();tab=[]
 def make(rem,lo):
  if not rem:
   if min(d)==4:
    t=tuple(sorted(tab))
    if all(t<=tuple(sorted(p[x]for x in t))for p in per):yield t
   return
  r=rem[0]
  for x in masks:
   if x<lo or x.bit_count()!=r:continue
   y=bits(x);pairs=list(combinations(y,2))
   if any(d[h]>=4 for h in y)or any(pp[k]>=2 for k in pairs):continue
   for h in y:d[h]+=1
   pp.update(pairs);tab.append(x)
   if min(d)+len(rem)-1>=4:yield from make(rem[1:],x+(r>2) if len(rem)>1 and rem[1]==r else 0)
   tab.pop();pp.subtract(pairs)
   for h in y:d[h]-=1
 for a in range(3):yield from make([4]*a+[3]*(10-2*a)+[2]*(1+a),0)
def forests(B):
 d=[x.bit_count()-2 for x in B];N=[set()for i in Z]
 def go(k):
  while k<11 and not d[k]:k+=1
  if k==11:
   for i in Z:
    for j in range(i):
     if (B[i]&B[j]).bit_count()+len(N[i]&N[j])>2-(j in N[i]):return
    for h in V:
     if sum(B[j]>>h&1 for j in N[i])>2-(B[i]>>h&1):return
    S={i};last=0
    while len(S)>last:last=len(S);S.update(set().union(*(N[v]for v in tuple(S))))
    if len(S)>4 or sum(len(N[v])for v in S)>=2*len(S):return
   yield tuple(tuple(sorted(x))for x in N);return
  good=[j for j in range(k+1,11) if d[j] and (B[k]&B[j]).bit_count()<=1]
  for J in combinations(good,d[k]):
   for j in J:d[j]-=1;N[k].add(j);N[j].add(k)
   d[k]-=len(J);yield from go(k+1);d[k]+=len(J)
   for j in J:d[j]+=1;N[k].remove(j);N[j].remove(k)
 yield from go(0)
# Reduced under the full D8 action, before embedding the cube, not a cube automorphism.
def B19(B,E):
 A=np.zeros((19,19),int)
 for i in Z:
  for j in E[i]:A[8+i,8+j]=1
  for h in bits(B[i]):A[8+i,h]=A[h,8+i]=1
 return A
def catalog():
 S=list(incidence());assert len(S)==63
 F=[(B,E)for B in S for E in forests(B)]
 assert Counter(sum(x.bit_count()==4 for x in B)for B,E in F)=={0:2693,1:785,2:43}
 return F

def bwords(M):
 A=M[16:,16:];R=12*np.eye(35,dtype=int)-M-M@M+2;R0=R[16:,16:]
 hos=[tuple(L) for j in range(5)for L in combinations(range(8),j) if all(R0[k,l]>0 for k,l in combinations(L,2))]
 words=[]
 for L in hos:
  ok=[i for i in range(8,19)if all(R0[h,i]>0 for h in L)]
  for Z0 in combinations(ok,len(L)+1):
   W=L+Z0
   if any(R0[i,j]<=0 for i,j in combinations(Z0,2)):continue
   if any(sum(A[j,k] for k in W)>1 for j in W):continue
   words.append(W)
 return words,R
def candidates(M):
 W,R=bwords(M);B=np.zeros((len(W),19),np.int8)
 for i,ww in enumerate(W):B[i,list(ww)]=1
 bad=(B @ (R[16:,:16]==0).astype(np.int8))>0
 # Additional core matching or row common quotas y against each physical cube+h+z site.
 # A candidate is invalid if a true core site j sees too many of its known neighbors in y's support.
 W0=[]
 for p in range(8):
  for n in range(8,16):
   if R[p,n]==0:continue
   t=np.flatnonzero(~(bad[:,p]|bad[:,n]))
   D=np.zeros((len(t),35),np.int8);D[:,16:]=B[t];D[:,p]=D[:,n]=1
   ok=~np.any(D@M>2-D,axis=1)
   W0.append(D[ok])
 return np.vstack(W0),R
def canon(F):
 out=[]
 from collections import defaultdict
 base=defaultdict(dict)
 for i,(b,e) in enumerate(F):base[b][e]=i
 for b,graphidx in base.items():
  zz=defaultdict(list)
  for j,m in enumerate(b):zz[m].append(j)
  ex=[]
  for f in [0,1]:
   d=1-2*f
   for r in range(8):
    bb=tuple(trans(x,r,f)for x in b)
    if sorted(bb)!=list(b):continue
    keys=sorted(zz)
    for tar in product(*(permutations(zz[v])for v in keys)):
     g=[-1]*11
     for v,t in zip(keys,tar):
      src=[i for i,z in enumerate(bb)if z==v]
      for i,j in zip(src,t):g[i]=j
     ex.append((r,d,g))
  for e,idx in graphidx.items():
   images=[]
   for r,d,g in ex:
    p=[None]*11
    for i,ne in enumerate(e):p[g[i]]=tuple(sorted(g[x]for x in ne))
    e0=tuple(p);images.append((graphidx[e0],r,d))
   for t,span in enumerate((1,1,1,1)):
    for s in range(span):
     if all((idx,s)<=(j,(d*s-r)%span)for j,r,d in images):out.append((idx,t,s))
 return sorted(out)

import sys
from time import time
def cached(fn):
 d={}
 def wrap(M):
  k=M.tobytes()
  if k not in d:d[k]=fn(M)
  return d[k]
 wrap.clear=d.clear;return wrap
bwords=cached(bwords);candidates=cached(candidates)
S=[(4355,4737,8896,9312,17456,49176,34828,2310),(8707,9345,17600,49248,34864,2328,4364,4614),(34819,2433,4544,4704,8752,9240,17420,49158),(49155,34945,2496,4448,4656,8728,9228,17414)]
OLD=(53,77,83,106,154,166,169,212)
def A35(old,t,shift):
 A=np.zeros((35,35),int);A[16:,16:]=old
 for j,word in enumerate(OLD):
  for i in bits(word):A[i,8+j]=A[8+j,i]=1
 for i in V:
  for j in bits(S[t][(i+shift)%8]):A[j,16+i]=A[16+i,j]=1
 return A

def tstar(M,allw,R,h,cap):
 # All eight known neighbors and six actual Y neighbors of this H site.
 hn=16+h;N=np.flatnonzero(M[hn]);assert len(N)==8
 ww=allw[(allw[:,hn]>0)&np.all(allw<=R[hn],axis=1)]
 n=len(ww);tar=list(map(int,R[hn]));ans=[];nodes=0
 cols=[sum(1<<int(i)for i in np.flatnonzero(r))for r in ww.T]
 msk=[sum(1<<int(j)for j in np.flatnonzero(v))for v in ww]
 bad=[];edgefree=[]
 for i,v in enumerate(msk):bad.append(sum(1<<j for j,y in enumerate(msk)if j==i or(v&y).bit_count()>2))
 # Enumerate unordered classes from the exact column margins.
 stk=[]
 def go(pool):
  nonlocal nodes;nodes+=1
  if len(ans)>=cap:return
  if len(stk)==6:
   if any(tar):return
   W=ww[stk]; AA=M[np.ix_(N,N)];nw=W[:,N];L=AA.sum(axis=0)+nw.sum(axis=0)
   if min(L)!=1 or max(L)!=1 or max(nw.sum(axis=1))>1:return
   if np.any(W.T@W>R):return
   free=[k for k,v in enumerate(nw.sum(axis=1))if v==0]
   if len(free)%2:return
   DD=W@W.T;D=np.zeros((6,6),dtype=np.int8)
   def mat(F):
    if not F:
     # Complete root matching candidates; retain only the first-star common-neighbor quotas.
     if np.any(DD+D@D+D>2+14*np.eye(6))or np.any(W@M+D@W>2-W):return
     ans.append((W,D.copy()));return
    i,*U=F
    for j in U:
     if DD[i,j]==1:
      D[i,j]=D[j,i]=1;mat([a for a in U if a!=j]);D[i,j]=D[j,i]=0
   mat(free);return
  need=[(pool&cols[j],j)for j,d in enumerate(tar)if d]
  if any(q.bit_count()<tar[j]for q,j in need):return
  q,v=min(need,key=lambda p:__import__('math').comb(p[0].bit_count(),tar[p[1]]))
  def select(opts,pool,k):
   if not k:go(pool);return
   opts&=pool
   while opts.bit_count()>=k and len(ans)<cap:
    bit=opts&-opts;opts-=bit;i=bit.bit_length()-1;pp=pool&~bad[i];W0=bits(msk[i]);ok=True
    for j in W0:
     tar[j]-=1
     if tar[j]==0:pp&=~cols[j]
     if tar[j]<0:ok=False
    if ok:
     stk.append(i);select(opts,pp,k-1);stk.pop()
    for j in W0:tar[j]+=1
  select(q,pool,tar[v])
 go((1<<n)-1);return ans,nodes
def oldneg(B):
 val,V=np.linalg.eigh(B)
 if val[0]<0:
  u=np.rint(V[:,0]*10000).astype(np.int64)
  if int(u@B@u)<0:return True
 return False
def psdwords(M,W):
 W=W.astype(np.int16)
 for B,k,d,b in [(27*np.eye(len(M),dtype=np.int64)-9*M+1,-9,28,1),(44*np.eye(len(M),dtype=np.int64)+11*M-2,11,42,-2)]:
  if oldneg(B):return W[:0]
  if not len(W):return W
  X=(W*k+b).astype(np.int64);A=np.linalg.solve(B+np.eye(len(M))/128,X.T).T
  # v and s are integer; the float calculation only proposes negative witnesses.
  scale=256
  V=np.rint(np.clip(A*scale,-100000,100000)).astype(np.int64)
  ok=(np.sum((V@B-2*scale*X)*V,axis=1)+d*scale*scale>=0)
  W=W[ok]
 return W
def rankfree(M):
 if oldneg(27*np.eye(35,dtype=np.int64)-9*M+1):return 0,0
 allw,R=candidates(M)
 W=psdwords(M,allw)
 if not len(W):return 0,0
 T=np.zeros((35,35),np.int64)
 for i in range(8):
  for j in range(8,16):
   n=R[i,j]
   if n<1:continue
   u=W[(W[:,i]>0)&(W[:,j]>0)].astype(np.int64)
   if len(u)<n:return 1,len(W)
   T+=np.minimum(n,u.T@u)
 if np.any(T<R):return 2,len(W)
 return 3,len(W)

def extend(M,W):
 R=12*np.eye(35,dtype=int)+2-M-M@M;W=psdwords(M,W)
 tt=sorted(range(8),key=lambda h:np.sum((W[:,16+h]>0)&np.all(W<=R[16+h],axis=1)))
 for h in tt:
  data,n=tstar(M,W,R,h,1000)
  if len(data)>=1000:continue
  possible=[]
  for B,U in data:
   J=np.block([[M,B.T],[B,U]]);R2=12*np.eye(41,dtype=int)+2-J-J@J
   if R2.min()<0 or oldneg(27*np.eye(41,dtype=np.int64)-9*J+1)or oldneg(44*np.eye(41,dtype=np.int64)+11*J-2):continue
   possible.append((B,U))
  if not possible:return 4 if len(data)==0 else 5
 return 6
def check_dihedral():
 # Whole core relabelings, including exchange of its two independent shores.
 W=OLD;rows=[sum(1<<j for j,w in enumerate(W)if w>>i&1)for i in range(8)]
 dirs=set()
 for swap,T in [(0,W),(1,rows)]:
  for p in permutations(range(8)):
   vs=[sum(1<<p[i]for i in bits(w))for w in W]
   if set(vs)!=set(T):continue
   q=[T.index(v)for v in vs]
   perm=[p[i]+8*swap for i in V]+[q[i]+8*(1-swap)for i in V]
   im=[sum(1<<perm[j]for j in bits(w))for w in S[0]]
   for r,d in product(V,(-1,1)):
    if im==[S[0][(r+d*j)%8]for j in V]:dirs.add((r,d))
 assert len(dirs)==16
def main():
 check_dihedral();F=catalog();C=canon(F);stats=Counter()
 for j,t,k in C:
  if t!=0:continue
  bwords.clear();candidates.clear();M=A35(B19(*F[j]),t,k);m,n=rankfree(M)
  if m==3:m=extend(M,candidates(M)[0])
  assert m in (0,1,2,4,5),(j,m)
  stats[m]+=1
 assert sum(stats.values())==2433
 print('Certified 2433/2433; counts by witness:',dict(sorted(stats.items())))
if __name__=='__main__':main()
