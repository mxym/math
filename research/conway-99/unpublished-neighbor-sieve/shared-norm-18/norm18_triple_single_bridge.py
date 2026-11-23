# Exact one-bridge exclusion. Python 3.10+, NumPy for small bounded integer products.
from functools import lru_cache
from itertools import combinations,product
from collections import Counter
from math import gcd
import sys
import numpy as np
from norm18_triple_core import core23,incidence,nside,reps,tables
# Pure integer Schur tests at a fixed 23-site core; the unknown tail has 5,10 or15 sites.
def pivots(G):
 a=[r[:] for r in G]; ids=[]; prev=1
 for k,v in enumerate(a):
  p=v[k]
  if p<0 or (p==0 and any(v[k+1:])):return None
  if not p:continue
  ids.append(k)
  for i in range(k+1,len(a)):
   r=a[i];c=v[i]
   for j in range(i,len(a)):
    r[j],rem=divmod(p*r[j]-c*v[j],prev);assert not rem
  prev=p
 return ids
def inv(G):
 n=len(G);a=[r[:]+[int(i==j)for j in range(n)]for i,r in enumerate(G)];prev=1
 for k,v in enumerate(a):
  p=v[k];assert p>0
  for i,r in enumerate(a):
   if i!=k:
    c=r[k]
    for j in [*range(k),*range(k+1,2*n)]:
     r[j],rem=divmod(p*r[j]-c*v[j],prev);assert not rem
    r[k]=0
  prev=p
 t=[r[n:] for r in a]
 assert all(a[i][j]==prev*(i==j) for i in range(n) for j in range(n))
 g=gcd(prev,*(v for r in t for v in r))
 return prev//g,[[v//g for v in r]for r in t]
class Cone:
 def __init__(self,A,T,sg):
  self.sg=sg;s=T.sum(0);self.base=(9504*np.eye(23,dtype=int)+352-2016*T.T@T+441*np.outer(s,s)-3168*A if sg==0 else 44*np.eye(23,dtype=int)+11*A-2).tolist()
  self.I=I=pivots(self.base)
  if I is None:return
  self.tmpl=[[int(352+2016*T[i,j]-441*s[j]) if not sg else -2 for j in range(23)]for i in range(3)]
  self.det,self.adj=inv([[self.base[u][w]for w in I]for u in I]);self.K=-3168 if not sg else 11
  self.lookup={};self.corr={}
 def vertex(self,v):
  if v in self.lookup:return self.lookup[v]
  i,m=v;I=self.I;b=[z+self.K*((m>>j)&1)for j,z in enumerate(self.tmpl[i])]
  y=[sum(a*b[q]for a,q in zip(r,I))for r in self.adj]
  if any(self.det*b[j]!=sum(self.base[j][q]*z for q,z in zip(I,y))for j in range(23) if j not in I):
   datum=None
  else:
   yy=[0]*23
   for j,g in zip(I,y):yy[j]=g
   datum=yy,[sum(a*g for a,g in zip(tmp,yy))for tmp in self.tmpl]
  self.lookup[v]=datum;return datum
 def val(self,v,w):
  pair=(v,w) if v<=w else (w,v)
  if pair not in self.corr:
   yy,off=self.vertex(v);i,m=w;z=off[i]
   while m:
    bit=m&-m;m-=bit;z+=self.K*yy[bit.bit_length()-1]
   std=793-2016*(v[0]==w[0]) if not self.sg else -2
   self.corr[pair]=self.det*std-z
  return self.corr[pair]
 def check(self,U,X):
  if any(self.vertex(v) is None for v in U):return False
  n=len(U); rows=[]
  for j,v in enumerate(U):
   r=[0]*j+[self.val(v,w)for w in U[j:]];r[j]+=self.det*(9504 if not self.sg else 44)
   bit=X[j] & ~((1<<(j+1))-1)
   while bit:
    b=bit&-bit;bit-=b;r[b.bit_length()-1]+=self.K*self.det
   rows.append(r)
  return pivots(rows) is not None
@lru_cache(None)
def nrows(ch,i):
 part,fs=reps()[ch][1]
 return [incidence(part,fs,i,r) for r in nside(part,fs,i)]
@lru_cache(None)
def xtab(rd,cd):
 ts=tables(rd,cd);X=np.zeros((len(ts),5,5),dtype=int)
 for k,t in enumerate(ts):
  for p,v in enumerate(t):X[k,p,list(v)]=1
 return X
def cmasks(M,i):
 return tuple((i,sum(1<<int(j)for j in np.flatnonzero(v))) for v in M.T)
def xbits(X):
 return [sum(1<<int(j) for j in np.flatnonzero(v))for v in X]
class Sweep:
 def __init__(self,ch,cc):
  self.ch=ch;self.cc=cc
  self.part,self.fs=reps()[ch][1]
 def chart(self,A,T,es):
  self.A=A;self.T=T;self.K=[Cone(A,T,s)for s in (0,1)]
  if any(c.I is None for c in self.K):return
  self.cc[23]+=1;self.G=[[]for h in range(3)]
  G=self.G; F=12*np.eye(23,dtype=int)+2-A-A@A
  for i in range(3):
   for base in nrows(self.ch,i):
    for w in (range(5) if i in es else [None]):
     M=base.copy()
     if w is not None:M[es[i],w]=1
     if (F-M@M.T).min()<0 or (A@M+M).max()>2 or np.max(M.T@M-4*np.eye(5,dtype=int))>2:continue
     U=cmasks(M,i)
     if all(c.check(U,[0]*5)for c in self.K):G[i].append((M,U))
   if not G[i]:return
  x,y,z=sorted(range(3),key=lambda h:len(G[h]));cache={}
  def pp(i,u,j,v):
   key=(i,u,j,v)
   if key in cache:return cache[key]
   M,U=G[i][u];N,V=G[j][v];O=[]
   if (F-M@M.T-N@N.T).min()>=0:
    mn=M.T@N;X=xtab(tuple(T[j]@M),tuple(T[i]@N))
    if len(X):
     X=X[((mn+X)<=2).all((1,2))&((A@M+M+N@X.transpose(0,2,1))<=2).all((1,2))&((A@N+N+M@X)<=2).all((1,2))]
     for w in X:
      S=[a<<5 for a in xbits(w)]+xbits(w.T)
      if all(c.check(U+V,S)for c in self.K):O.append(w)
   cache[key]=O;return O
  # joined exact pair tables
  for ix,(M,U) in enumerate(G[x]):
   for iy,(N,V) in enumerate(G[y]):
    P=pp(x,ix,y,iy)
    if not P:continue
    for iz,(O,W) in enumerate(G[z]):
     f=F-M@M.T-N@N.T-O@O.T
     if f.min()<0 or any(f[5+s,5+t]>1 for s,t in self.part):continue
     Q=pp(x,ix,z,iz)
     if not Q:continue
     R=pp(y,iy,z,iz)
     if not R:continue
     for a,b,c in product(P,Q,R):
      # full pairwise codegrees, including connections through a third private group
      B=np.concatenate((M,N,O),axis=1);zero=np.zeros((5,5),dtype=int)
      X=np.block([[zero,a,b],[a.T,zero,c],[b.T,c.T,zero]])
      if np.max(A@B+B@X+B)>2 or np.max(B.T@B+X@X+X-14*np.eye(15,dtype=int))>2:continue
      self.cc[38]+=1
      S=xbits(X)
      if all(k.check(U+V+W,S)for k in self.K):self.cc['survivors']+=1
def run(ch):
 part,fs=reps()[ch][1];base,T=core23(part,fs);cc=Counter();g=Sweep(ch,cc)
 for i,j in combinations(range(3),2):
  for u in range(11+4*i,15+4*i):
   for v in range(11+4*j,15+4*j):
    A=base.copy();A[u,v]=A[v,u]=1;cc[0]+=1
    if np.min(12*np.eye(23,dtype=int)+2-A-A@A)<0:continue
    g.chart(A,T,{i:v,j:u})
 print(ch,cc[0],cc[23],cc[38],cc['survivors'],flush=True)
 return cc

if __name__=='__main__':
 expected23=[7,12,10,14,3,5,10,14,14,8,24,27,20,30,12,28,16,38,38,36,40,16,16,9,37,42,39,41,38,39,41,44,40,48]
 expected38={7:2,21:10,22:36,27:2,30:4,31:20}
 assert len(reps())==34 and sum(expected23)==856 and sum(expected38.values())==74
 for ch in (list(map(int,sys.argv[1:])) or range(34)):
  assert 0<=ch<34
  c=run(ch);assert (c[0],c[23],c[38],c['survivors'])==(48,expected23[ch],expected38.get(ch,0),0)
