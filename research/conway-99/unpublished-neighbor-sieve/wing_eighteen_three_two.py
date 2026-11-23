"""Exact separation of all 9,726 orbit tables in an 18+18 mixed wing split.
Python (NumPy and SciPy sparse integer multiplication only). No LP solver or floating computation.
"""
from itertools import permutations,product,combinations
from collections import Counter,defaultdict
import numpy as np
I=tuple(range(6));P=(1,0,3,2,5,4)
def blocks(q,r,f):
 N=[set() for i in range(18)]
 for i in I:
  for a,b in [(i,P[i]),(i+6,6+q[i]),(12+i,12+r[i]),(i,6+i),(6+i,12+i),(12+i,f[i])]:
   N[a].add(b);N[b].add(a)
 return N
def kval(G):
 A=[[3*(i==j)-int(j in G[i]) for j in range(18)] for i in range(18)]+[[1]*18]
 return kernel(A)
def kernel(a):
    A=[[v%7 for v in r] for r in a];m=len(A);n=len(A[0]);piv=[]
    for j in range(n):
        t=len(piv);r=next((i for i in range(t,m) if A[i][j]),None)
        if r is None:continue
        A[t],A[r]=A[r],A[t];inv=pow(A[t][j],-1,7)
        A[t]=[v*inv%7 for v in A[t]]
        for i in range(m):
            if i!=t:
                q=A[i][j];A[i]=[(v-q*u)%7 for v,u in zip(A[i],A[t])]
        piv.append(j)
    B=[]
    for f in sorted(set(range(n))-set(piv)):
        x=[0]*n;x[f]=1
        for i,j in enumerate(piv):x[j]=-A[i][f]%7
        B.append(tuple(x))
    return B




def automorphisms(G):
 # A permutation of the three wings and of six sites of the first wing determines any isomorphism:
 # images in each of the other wings are forced by the cross-wing perfect matchings.
 for w in permutations(range(3)):
  for p in permutations(range(6)):
   z=[None]*18
   for i in range(6):z[i]=6*w[0]+p[i]
   for u in (1,2):
    for i in range(6):
     j,=(x for x in G[i] if x//6==u)
     v,=(x for x in G[z[i]] if x//6==w[u])
     z[j]=v
   if all({z[j] for j in G[i]}==G[z[i]] for i in range(18)):yield w,z
rr=(2,4,0,5,1,3),(1,0,5,4,3,2)
G=blocks(*rr,(3,5,4,1,2,0));K=kval(G);assert len(K)==3
autos=list(automorphisms(G))
assert len(autos)==12 and len({w for w,z in autos})==6
assert any(w==(0,1,2) and all((h[i]+h[z[i]])%7==0 for i in range(18) for h in K) for w,z in autos)
A=(G,K)
H=blocks(*rr,(4,3,1,0,2,5));B=H,kval(H)
def setup(S):
 G,K=S;m={(i,j):2-int(j in G[i])-len(G[i]&G[j])-int(i//6==j//6) for i,j in combinations(range(18),2)};pp=[v for v,mv in m.items() if mv>0]
 E=[v for v in combinations(range(18),3) if all(m[k]>0 for k in combinations(v,2)) and len({i//6 for i in v})>=2 and all(len(G[i].intersection(v))+int(i in v)<=2 for i in range(18))]
 K=np.array(K);sig=np.array([K[:,list(e)].sum(axis=1)%7 for e in E]);wing=np.array([sum(4**i*sum(v//6==i for v in e) for i in range(3)) for e in E]);rows=[[pp.index(q) for q in combinations(e,2)] for e in E]
 return E,pp,m,sig,wing,rows
AA,BB=setup(A),setup(B);assert len(A[1])==3 and len(B[1])==2 and (len(AA[0]),len(BB[0]))==(612,578)
import time
from scipy.sparse import csc_matrix
E,p,m,Z,w,rr=BB;F,q,n,Y,u,ss=AA;O=len(p)+len(q)
pfull=[m[x] for x in p]+[n[x] for x in q]+[2-int(i//6==j//6) for i in range(18) for j in range(18)];rhs=np.array(pfull,int);nr=len(rhs)
assert sum(rhs)==900 and max(rhs)==2

def rs(M):
 y=(Y@M.T%7); v=(7*y[:,0]+y[:,1])+49*(42-u);x=7*Z[:,0]+Z[:,1]+49*w
 order=np.argsort(v);v=np.array(v[order]);a=np.searchsorted(v,x);b=np.searchsorted(v,x,side='right');ii=np.repeat(np.arange(len(E)),b-a);jj=order[np.arange(len(ii))+np.repeat(a-np.cumsum(b-a)+(b-a),b-a)]
 return np.hstack((np.array(rr)[ii],len(p)+np.array(ss)[jj],(O+18*np.array(E)[ii,:,None]+np.array(F)[jj,None,:]).reshape(-1,9))).astype(np.int32)
def sep(M,cap=3000):
 rows=rs(M);N=len(rows);j=np.arange(0,15*N+1,15,dtype=np.int32);mat=csc_matrix((np.ones(15*N,dtype=np.int64),rows.reshape(-1),j),shape=(nr,N))
 # Deterministically search for an integer separator by a scaled integer residual iteration.
 # No convergence guarantee is assumed: only the strictly verified dot-product certificate accepts.
 maxit=cap;D=1<<20;R=rhs*D;L=15*int(np.bincount(rows.reshape(-1),minlength=nr).max())
 z=x=np.zeros(N,dtype=np.int64)
 for k in range(1,maxit+1):
  v=mat@z-R;jj=mat.T@v
  y=np.maximum(0,z-np.floor_divide(jj+L//2,L))
  z=y+np.floor_divide((k-1)*(y-x),k+2);x=y
  if k%16==0:
   v=mat@x-R
   assert np.all((-(1<<42)<v)&(v<(1<<42)))  # dot products below stay exact in signed int64
   m0=int(v@rhs);v0=int(v[rows].sum(1).min())
   if m0<60*v0:return k
 return None
def invmat(Q):
 n=len(Q);A=np.concatenate((np.array(Q,int),np.eye(n,dtype=int)),axis=1)%7
 for i in range(n):
  j=next(j for j in range(i,n) if A[j,i]);A[[i,j]]=A[[j,i]]
  A[i]=A[i]*pow(int(A[i,i]),-1,7)%7
  for j in range(n):
   if i!=j:A[j]=(A[j]-A[j,i]*A[i])%7
 return A[:,n:]
def rep(g,k):
 B=np.array(k,int);b=len(B)
 for col in combinations(range(18),b):
  try:T=invmat(B[:,list(col)])
  except StopIteration:continue
  break
 for w,z in automorphisms(g):
  r=B[:,z][:,list(col)]@T%7
  assert np.array_equal(B[:,z],r@B%7)
  yield w,r
g=[(u,invmat(v)) for x,u in rep(*B) for y,v in rep(*A) if x==y]
assert len(g)==12
ints=(7**np.arange(6)).reshape(2,3);cl=np.array(list(product(range(7),repeat=3)),dtype=np.int64)
c0=np.cross(cl[:,None,:],cl[None,:,:]);ix,iy=np.nonzero(np.any(c0%7,axis=2))
maps=np.array([cl[ix],cl[iy]]).transpose(1,0,2);code=np.sum(maps*ints,axis=(1,2))
yes=np.ones(len(maps),bool)
for gleft,gright in g:
 r=np.sum((gleft@maps@gright%7)*ints,axis=(1,2));yes &= code<=r
maps=maps[yes]
assert (len(ix),len(maps))==(114912,9726)
print('exact orbit count:',len(maps),'from',len(ix),'maps',flush=True)
worst=0;t0=time.monotonic()
for idx,M in enumerate(maps,1):
 k=sep(M);assert k is not None,("unseparated",M.tolist())
 worst=max(worst,k)
 if idx%2000==0:print('strict integer separators:',idx,'/',len(maps),flush=True)
print('all 9726 pair-incidence tables impossible; max steps',worst,'seconds',round(time.monotonic()-t0,2))
