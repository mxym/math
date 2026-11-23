"""Every clean cell off a saturated axis has four F7 residuals spanning dimension three.
Only integer operations and an exact linear separation check are used. Python, NumPy, SciPy sparse.
"""
import numpy as np
from itertools import permutations,combinations,product
from collections import Counter
W=np.array(sorted(set(permutations((0,0,1,1,2,2)))),int);H=np.array(list(product(range(2),repeat=6)),int)
T=(2*W[:,None,:]+H[None,:,:]).reshape(-1,6)
pairs=list(combinations(range(6),2));ql=np.array([36*i+6*T[:,a]+T[:,b] for i,(a,b) in enumerate(pairs)]).T
def ag(q0):
 a=(T==q0).sum(1);k=(T//2==q0//2).sum(1);c=((T//2!=q0//2)&(T%2==q0%2)).sum(1)
 return a,k-a,c,(43-18*a-4*k-6*c)%7
def D(q0):return np.array([[2-int(v==q0[j])-int((v//2==q0[j]//2 and v!=q0[j]) or (v//2!=q0[j]//2 and v%2==q0[j]%2)) for v in range(6)] for j in range(6)]).reshape(-1)

from itertools import combinations_with_replacement
from scipy.sparse import coo_matrix
Xid={tuple(r):i for i,r in enumerate(T)}
perms=[p for p in permutations(range(2,6)) if p[0]%2==0]
def charts():
 out=[]
 for ls in combinations_with_replacement(perms,4):
  X=np.column_stack((np.array([0,0,1,1]),np.array([0,1,0,1]),np.array(ls).T))
  if not np.all((X//2==1).sum(1)==2):continue
  Id=np.array([Xid[tuple(t)] for t in X]);nmat=[];V=[]
  near=np.array([[int(j!=i and ((i^j) in (1,2))) for j in range(4)] for i in range(4)])
  for q0 in X:
   a,b,c,v=ag(q0);V.append(v);nmat.append(a)
  V=np.array(V);nmat=np.array(nmat)
  R=(V[:,Id]-4*near)%7;np.fill_diagonal(R,0)
  out.append((X,Id,nmat,V,near,R))
 return out
def ftest(X,Id,nn,V,near,lam,cap):
 mask=(nn<=2).all(0)&~np.all(T[:,:2]//2==0,axis=1)
 must=np.all(T[:,:2]//2!=0,axis=1);mv=(lam@V)%7
 zz=[];E=[]
 for j in range(-1,4):
  A=mask & ((mv-4*(lam[j] if j>=0 else 0))%7==0)&(must==(j>=0))
  if j>=0:A&=nn[j]<=1
  ix=np.flatnonzero(A);zz.extend(ix);E.extend([j]*len(ix))
 zz=np.array(zz);E=np.array(E);N=len(zz)
 if not N:return 0
 row=np.arange(N);ii=[ql[zz].reshape(-1)];jj=[np.repeat(row,15)]
 for j in range(4):
  ok=E==j;ii.append((540+36*j+6*np.arange(6)[None,:]+T[zz[ok]]).reshape(-1));jj.append(np.repeat(row[ok],6))
 m=2*np.ones(540,int)
 for k,(a,b) in enumerate(pairs):m[36*k:36*k+36]-=(np.arange(6)[:,None]//2==np.arange(6)[None,:]//2).reshape(-1)
 r=np.r_[m-np.bincount(ql[Id].reshape(-1),minlength=540),np.concatenate([D(X[j])-np.eye(6,dtype=int)[X[near[j]==1]].sum(0).reshape(-1) for j in range(4)])]
 ii=np.concatenate(ii);jj=np.concatenate(jj)
 mat=coo_matrix((np.ones(len(ii),dtype=np.int64),(ii,jj)),shape=(684,N)).tocsr()
 # Candidate-independent exact separation check: all 56 other sites have to contribute a column.
 # The iterative search only proposes an integer w; no convergence statement is used.
 assert min(r)>=0 and sum(r)==984 # 56*15 pair contacts and 4*6*6 outside-neighbor contacts
 scale=1<<20;L=21*int(np.bincount(ii,minlength=684).max());z=u=np.zeros(N,dtype=np.int64)
 for k in range(1,cap+1):
  wt=mat@z-scale*r;v=np.maximum(0,z-(mat.T@wt+L//2)//L);z=v+((k-1)*(v-u))//(k+2);u=v
  if k%16==0:
   w=mat@u-scale*r
   assert np.all((-1<<40)<w) and np.all(w<(1<<40))
   if int(w@r)<56*int((mat.T@w).min()):return k
 return -1

lines=[np.array([*l,0]) for l in product(range(7),repeat=3) if any(l) and next(v for v in l if v)==1]
Cs=charts();print('raw',len(Cs))
import time;t0=time.monotonic();tally=Counter();un=[];mx=0
for i,(X,Id,nn,V,near,R) in enumerate(Cs):
 possible=[l for l in lines if np.all((R@l)%7==0)];tally[len(possible)]+=1
 for L in possible:
  k=ftest(X,Id,nn,V,near,L,5000);mx=max(mx,k)
  if k<0:un.append((i,L.tolist()))
assert len(Cs)==75 and tally=={0:34,1:36,57:5} and not un
print('321 linear relations rejected; candidate counts',tally,'maximum steps',mx,'seconds',time.monotonic()-t0)
