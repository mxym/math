import numpy as np
from itertools import combinations
P=101
n=27
def create():
 T=np.zeros((n,n,n),dtype=np.int64)
 def into(i,vec):
  a=np.zeros(n,dtype=np.int64)
  a[0]=vec[0]
  a[1+4*i:5+4*i]=np.array(vec[1:])-vec[0]*np.array([1,-2,1,1])
  return a
 c=np.eye(n,dtype=np.int64)[0]
 a=[into(i,[1,1,-2,-1,-1]) for i in range(2)]
 for z in [*a,c]: T+=np.einsum('i,j,k->ijk',z,z,z)
 for i in range(2):
  for r in range(3):
   for s in range(3):
    w0=np.zeros(5,dtype=np.int64);w0[r]=1
    if s<2:w0[3+s]=-2
    w=into(i,w0)
    e=np.eye(n,dtype=np.int64)[9+9*i+3*r+s]
    lam=(1,1,-2)[r]*(1,1,-2)[s]
    x=np.einsum('i,j,k->ijk',e,w,w)
    T+=lam*(x+x.transpose(1,0,2)+x.transpose(1,2,0))
 return T
def kos(T,r,p,seed=7):
 rng=np.random.default_rng(seed)
 A=rng.integers(P,size=(r,n))
 TT=(A @ T.reshape(n,n*n)).reshape(r,n,n)
 U=list(combinations(range(r),p));V={v:i for i,v in enumerate(combinations(range(r),p+1))}
 M=np.zeros((len(V)*n,len(U)*n),dtype=np.int64)
 for j,u in enumerate(U):
  for a in range(r):
   if a not in u:
    i=V[tuple(sorted((a,*u)))]
    M[i*n:i*n+n,j*n:j*n+n]=((-1)**sum(b<a for b in u)*TT[a].T)%P
 return M
def mod_rank(M):
 # row selection and modular block elimination
 r=0
 for j in range(M.shape[1]):
  hits=np.flatnonzero(M[r:,j])
  if hits.size:
   u=r+hits[0]
   if u!=r: M[[r,u],j:]=M[[u,r],j:]
   piv=M[r,j:]*pow(int(M[r,j]),-1,P)%P
   hits=hits[1:]+r
   M[hits,j:]=(M[hits,j:]-M[hits,j,None]*piv)%P
   r+=1
   if r==M.shape[0]: break
 return r
if __name__=='__main__':
 from math import comb,ceil
 T=create()
 assert mod_rank(T.reshape(n,-1)%P)==27
 for r,p in [(6,2)]:
  M=kos(T,r,p)
  d=mod_rank(M)
  assert d == 286
  print(r,p,M.shape,d,ceil(d/comb(r-1,p)),flush=True)
