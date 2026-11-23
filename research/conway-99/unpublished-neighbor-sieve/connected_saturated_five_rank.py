#!/usr/bin/env python3
"""Exact F5 certificate for connected saturated-triangle contractions; Python 3 + NumPy, no solver."""
import itertools as it, collections, math
from collections import Counter
def parts(n,lo=1):
 if not n:yield ();return
 for k in range(lo,n+1):
  for z in parts(n-k,k):yield (k,)+z
def perfect(V):
 if not V:yield ();return
 x=V[0]
 for j in range(1,len(V)):
  for e in perfect(V[1:j]+V[j+1:]):yield ((x,V[j]),)+e
def mate(E,n):
 out=[-1]*n
 for x,y in E:out[x]=y;out[y]=x
 return tuple(out)
def key(A):
 n=len(A[0]); best=None
 for i in range(n):
  o=[i];p=[-1]*n;p[i]=0;L=[]
  for x in o:
   for row in A:
    j=row[x]
    if p[j]<0:p[j]=len(o);o.append(j)
    L.append(p[j])
  if len(o)<n:return
  L=bytes(L)
  if best is None or L<best:best=L
 return best
def ks(n):
 p=list(range(n));F=tuple(mate(e,n) for e in perfect(tuple(p))); out=set()
 for z in parts(n//2):
  col0=[];col1=[]; l=0
  for k in z:
   for i in range(k):col0.append((l+2*i,l+2*i+1));col1.append((l+2*i+1,l+((2*i+2)%(2*k))))
   l+=2*k
  a,b=mate(col0,n),mate(col1,n)
  for c in F:
   A=(a,b,c); code=key(A)
   if code is not None and code not in out:
    # first canonicalize unrestricted color permutations and mark all their codes
    codes=set(key(tuple(A[j] for j in v)) for v in it.permutations(range(3)))
    out.update(codes);yield min(codes)
def rr(M):
 M=[list(row) for row in M]; nr=len(M);nc=len(M[0]);k=0;ps=[]
 for j in range(nc):
  a=next((i for i in range(k,nr) if M[i][j]%5),None)
  if a is None:continue
  M[a],M[k]=M[k],M[a]; u=pow(int(M[k][j]%5),-1,5)
  M[k]=[(x*u)%5 for x in M[k]]
  for i in range(nr):
   if i!=k and M[i][j]%5:
    a=M[i][j];M[i]=[(x-a*y)%5 for x,y in zip(M[i],M[k])]
  ps.append(j);k+=1
 return M[:k],ps
def null5(M):
 R,p=rr(M);out=[]
 for j in set(range(len(M[0])))-set(p):
  v=[0]*len(M[0]);v[j]=1
  for i,c in enumerate(p):v[c]=-R[i][j]%5
  out.append(v)
 return out
def cay(code):
 n=len(code)//3
 return [tuple(code[i*3+w] for i in range(n)) for w in range(3)]
import numpy as np
from functools import lru_cache
def diag(Z):
 Z=Z.copy();n=len(Z)
 for k in range(n):
  P=Z[k:];G=P@P.T%5
  if not G.any():break
  if not G.diagonal().any():
   a,b=np.argwhere(G!=0)[0];P[a]=(P[a]+P[b])%5
  else:a=np.flatnonzero(G.diagonal())[0]
  Z[[k,k+a]]=Z[[k+a,k]]
  d=Z[k]@Z[k]%5
  if d in (4,3):Z[k]=Z[k]*2%5;d=Z[k]@Z[k]%5
  assert d in [1,2]
  for i in range(k+1,n):Z[i]=(Z[i]-(Z[i]@Z[k])*pow(int(d),-1,5)*Z[k])%5
 v=np.diag(Z@Z.T%5);pairs=list(np.where(v==2)[0])
 for a,b in zip(pairs[::2],pairs[1::2]):
  Z[[a,b]]=(2*np.array([Z[a]+Z[b],Z[a]-Z[b]]))%5
 v=np.diag(Z@Z.T%5)
 o=sorted(range(n),key=lambda i:{0:3,1:1,2:2}[v[i]])
 Z=Z[o];G=Z@Z.T%5
 assert np.array_equal(G,np.diag(G.diagonal()))
 return Z,tuple(map(int,G.diagonal()))
@lru_cache(None)
def MaxIso(v):
 n=len(v)
 if n==0:return [np.zeros((0,0),int)]
 k=(n//2)-(n%2==0 and v[-1]==2) # -1 square in F5
 ret=[]
 for I in it.combinations(range(n),k):
  L=[]
  for j in I:
   F=[l for l in range(j+1,n) if l not in I]; choices=[]
   for t in it.product(range(5),repeat=len(F)):
    r=np.zeros(n,int);r[j]=1;r[F]=t
    if np.dot(r*r,v)%5==0:choices.append(r)
   L.append(choices)
  def rec(rows):
   if len(rows)==k:ret.append(np.array(rows,int).reshape((k,n)));return
   for row in L[len(rows)]:
    if all(np.dot(row*old,v)%5==0 for old in rows):rec(rows+[row])
  rec([])
 return ret
@lru_cache(None)
def lines(k):
 return np.array([(*((0,)*j),1,*t) for j in range(k) for t in it.product(range(5),repeat=k-j-1)],dtype=int)
def cyc(K):
 A=cay(K);n=len(A[0])
 E=[(i,a[i]) for a in A for i in range(n) if i<a[i]]
 Inc=[[int(i==a)-int(i==b) for a,b in E] for i in range(n)]
 return E,np.array(null5(Inc),int)
def survivors(K,k=4):
 E,Z=cyc(K);Z,v=diag(Z);rank=sum(bool(i) for i in v);rad=Z[rank:]
 w=v[:rank];n=rank;t=n//2-(n>0 and n%2==0 and w[-1]==2)
 if len(rad)+t<k:return
 for U in MaxIso(w):
  Y=np.concatenate([U@Z[:rank]%5,rad])
  line=lines(len(Y)); wt=np.count_nonzero(line@Y%5,axis=1)
  if len(Y)==k:
   if np.all(wt>=10):yield Y
  elif len(Y)==k+1:
   bad=line[wt<10]
   ok=np.all(bad@line.T%5!=0,axis=0)
   for u in line[ok]:
    yield np.array(null5([list(u)]))@Y%5
  else:raise AssertionError

from functools import lru_cache
@lru_cache(None)
def sumtable(k):
 F=np.array(list(it.product(range(5),repeat=k)),dtype=np.int16)
 wt=5**np.arange(k-1,-1,-1)
 return np.array(((-F[:,None,:]-F[None,:,:])%5)@wt,dtype=np.int32)
def charts(K):
 E,Z=cyc(K);n=len(K)//3;assert n==12
 O=[];B=[]
 for w in range(3):
  ww=[];bb=[]
  for i,j in it.combinations(range(6*w,6*w+6),2):
   for s,t in it.product([1,-1],repeat=2):
    x=np.zeros(18,dtype=np.int32);x[i]=s;x[j]=t;ww.append(x)
    ca=E[i][0 if s==1 else 1];cb=E[j][0 if t==1 else 1]
    bb.append(1<<ca|1<<cb)
  O.append(ww);B.append(bb)
 return np.array(O,dtype=np.int32),np.array(B,dtype=np.int32)
def breakplane(Y,O,B):
 k=len(Y);wt=5**np.arange(k-1,-1,-1);tar=sumtable(k)
 L=(O@Y.T%5)@wt
 # naked sumset three ways
 for i,j,w in [(0,1,2),(1,2,0),(2,0,1)]:
  D=tar[np.ix_(L[i],L[j])];counts=np.bincount(L[w],minlength=5**k)
  allowed=(counts[D]>0)&((B[i,:,None]&B[j,None,:])==0)
  if not np.all(allowed.any(axis=1)):return 1
 D=tar[np.ix_(L[0],L[1])]
 a,b,c=np.nonzero((D[:,:,None]==L[2][None,None,:]) & ((B[0,:,None,None]&B[1,None,:,None])==0)& ((B[0,:,None,None]&B[2,None,None,:])==0)& ((B[1,None,:,None]&B[2,None,None,:])==0))
 if not all(len(np.unique(x))==60 for x in (a,b,c)):return 2
 return 0

def crosscheck(Y,O,B,K):
 k=len(Y); wt=5**np.arange(k-1,-1,-1);L=(O@Y.T%5)@wt
 E,_=cyc(K);tail=[t for e in E for t in e];col=np.arange(36)//12
 D=np.array([[int(x!=y and (tail[x]==tail[y] or x//2==y//2)) for x in range(36)] for y in range(36)])
 M=2-D-D@D-(col[:,None]==col[None,:]).astype(int); np.fill_diagonal(M,0)
 assert np.min(M)>=0
 a,b,c=np.nonzero((sumtable(k)[np.ix_(L[0],L[1])][:,:,None]==L[2][None,None,:]) & ((B[0,:,None,None]&B[1,None,:,None])==0)& ((B[0,:,None,None]&B[2,None,None,:])==0)& ((B[1,None,:,None]&B[2,None,None,:])==0))
 tag=np.array([[sorted(2*i+int(s[i]<0) for i in np.flatnonzero(s)) for s in w] for w in O],int)
 darts=np.concatenate([tag[0,a],tag[1,b],tag[2,c]],axis=1)
 ii,jj=np.triu_indices(6,1); good=np.all(M[darts[:,ii],darts[:,jj]]>0,axis=1);dat=darts[good];keys=[a[good],b[good],c[good]]
 co=36*np.minimum(dat[:,ii],dat[:,jj])+np.maximum(dat[:,ii],dat[:,jj]);Q=np.triu(M).ravel()
 if np.any(np.bincount(co.ravel(),minlength=36**2)<Q):return 3
 for key in keys:
  U=np.unique(co*60+key[:,None])//60
  if np.any(np.bincount(U,minlength=36**2)<Q):return 4
 return 0

def main():
 rejected=Counter();rc=Counter();n=0;with_can=0
 for K in ks(12):
  O,B=charts(K);found=False
  _,v=diag(cyc(K)[1]);rc[v.count(0)]+=1
  for Y in survivors(K):
   found=True
   assert Y.shape==(4,18)
   assert len(rr(Y)[1])==4 and np.all(Y@Y.T%5==0)
   reason=breakplane(Y,O,B) or crosscheck(Y,O,B,K)
   assert reason in (1,2,3,4),(K.hex(),Y.tolist())
   rejected[reason]+=1
  n+=1;with_can+=found
 assert n==580 and rc=={0:352,1:196,2:24,3:8},(n,rc)
 assert with_can==134 and rejected=={1:20581,2:3756,3:142,4:8},(with_can,rejected)
 print("Connected colored K:",n,"bicycle radical census:",sorted(rc.items()))
 print("K with a polar/support candidate:",with_can,"candidate occurrences:",sum(rejected.values()),"rejections:",sorted(rejected.items()))
if __name__=='__main__':main()
