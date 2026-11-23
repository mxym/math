"""Rank-36 D3+A12+prism exclusion and single-current B12 orientation cut.
No external inputs, floating math, or optimization solver. NumPy/SciPy integer sparse products.
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




rr=(2,4,0,5,1,3),(1,0,5,4,3,2)
G=blocks(*rr,(3,5,4,1,2,0));K=kval(G);assert len(K)==3
A=(G,K)

def setup(S):
 G,K=S;m={(i,j):2-int(j in G[i])-len(G[i]&G[j])-int(i//6==j//6) for i,j in combinations(range(18),2)};pp=[v for v,mv in m.items() if mv>0]
 E=[v for v in combinations(range(18),3) if all(m[k]>0 for k in combinations(v,2)) and len({i//6 for i in v})>=2 and all(len(G[i].intersection(v))+int(i in v)<=2 for i in range(18))]
 K=np.array(K);sig=np.array([K[:,list(e)].sum(axis=1)%7 for e in E]);wing=np.array([sum(4**i*sum(v//6==i for v in e) for i in range(3)) for e in E]);rows=[[pp.index(q) for q in combinations(e,2)] for e in E]
 return E,pp,m,sig,wing,rows
def small12(f):
 n=4;g=[set() for j in range(12)]
 P=(1,0,3,2);Q=(2,3,0,1)
 for i in range(4):
  for x,y in ((i,P[i]),(i+4,Q[i]+4),(i+8,P[i]+8),(i,i+4),(i+4,i+8),(i+8,f[i])):
   g[x].add(y);g[y].add(x)
 L=[[3*int(i==j)-int(j in g[i]) for j in range(12)] for i in range(12)];kb=kernel(L+[[1]*12])
 return g,kb
import time
from scipy.sparse import csc_matrix
E,pp,m,Y,wa,rr=setup(A);za=np.array(E,int);all2=set(combinations(range(36),2))
def reg36(f):
 g,k=small12(f);pr=[set() for j in range(6)]
 for i in range(6):pr[i]={i^1}|{j for j in range(6) if (j%2==i%2 and j!=i)}
 gf=[set(x) for x in A[0]]+[{j+18 for j in x} for x in g]+[{j+30 for j in x} for x in pr]
 wing=[i//6 for i in range(18)]+[i//4 for i in range(12)]+[i//2 for i in range(6)]
 raw={(i,j):2-int(j in gf[i])-len(gf[i]&gf[j])-int(wing[i]==wing[j]) for i,j in sorted(all2)}
 rows=[p for p in raw if raw[p]];rhs=np.array([raw[p] for p in rows]);assert sum(rhs)==900 and min(rhs)==1
 idx=np.zeros((36,36),int)-1
 for h,(i,j) in enumerate(rows):idx[i,j]=idx[j,i]=h
 pair=[(i,j) for i,j in combinations(range(12),2) if raw[(i+18,j+18)]>0]; ps=np.array(pair)
 Z=np.array(k)[:,ps].sum(axis=2).T%7
 tup=[];ij=[]
 for i,e in enumerate(E):
  for j,x in enumerate(pair):
   h=e+tuple(18+v for v in x);ws=[2-sum(wing[v]==w for v in h) for w in range(3)]
   if min(ws)<0:continue
   w=ws.index(1)
   for p in (30+2*w,31+2*w):
    e0=h+(p,);tup.append([idx[v,w] for v,w in combinations(e0,2)]);ij.append((i,j))
 mat=np.array(tup,np.int32);ij=np.array(ij,np.int32)
 assert np.min(mat)>=0
 return rhs,Z,mat,ij

def sep(M,b,imax=1024):
 rhs,Z,allrows,ij=b;gv=Y@M.T%7;rows=allrows[np.all(gv[ij[:,0]]==Z[ij[:,1]],axis=1)];nr=len(rhs);N=len(rows)
 if not N:return 0
 j=np.arange(0,15*N+1,15,dtype=np.int32);mat=csc_matrix((np.ones(15*N,dtype=np.int64),rows.reshape(-1),j),shape=(nr,N))
 D=1<<18;R=rhs*D;L=15*int(np.bincount(rows.reshape(-1),minlength=nr).max());z=x=np.zeros(N,dtype=np.int64)
 for k in range(1,imax+1):
  v=mat@z-R;y=np.maximum(0,z-(mat.T@v+L//2)//L);z=y+((k-1)*(y-x))//(k+2);x=y
  if k%16==0:
   v=mat@x-R
   assert np.all((v>-(1<<42))&(v<(1<<42)))
   if int(v@rhs)<60*int(v[rows].sum(1).min()):return k
   if max(abs(v))<30:return None
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
 for w,z in aut(g):
  r=B[:,z][:,list(col)]@T%7
  assert np.array_equal(B[:,z],r@B%7)
  yield w,r

def aut(g):
 n=len(g);s=n//3
 for w in permutations(range(3)):
  for p in permutations(range(s)):
   z=[None]*n
   for i in range(s):z[i]=s*w[0]+p[i]
   for u in (1,2):
    for i in range(s):
     j,=(x for x in g[i] if x//s==u);v,=(x for x in g[z[i]] if x//s==w[u]);z[j]=v
   if all({z[j] for j in g[i]}==g[z[i]] for i in range(n)):yield w,z
def charts(d,f):
 assert {w for w,_ in aut(A[0])}==set(permutations(range(3)))
 g=[(a,invmat(b)) for w,a in rep(*small12(f)) for z,b in rep(*A) if w==z]
 cl=np.array(list(product(range(7),repeat=3)),dtype=np.int64);c0=np.cross(cl[:,None,:],cl[None,:,:]);ix,iy=np.nonzero(np.any(c0%7,axis=2))
 maps=np.array([cl[ix],cl[iy]]).transpose(1,0,2) if d==2 else cl[1:,None,:]
 ints=(7**np.arange(d*3)).reshape(d,3); code=np.sum(maps*ints,axis=(1,2));yes=np.ones(len(maps),bool)
 for a,b in g:yes &= code<=np.sum((a@maps@b%7)*ints,axis=(1,2))
 print('g',len(g),'orbits',sum(yes),'maps',len(maps),flush=True)
 return maps[yes]
for d,f in ((1,(0,3,2,1)),(2,(0,2,1,3))):
 b=reg36(f);maps=charts(d,f);un=[];st=0;t=time.monotonic()
 for i,M in enumerate(maps):
  k=sep(M,b)
  if k is None:un.append(M.reshape(-1).tolist())
  else:st=max(st,k)
  if i>0 and i%3000==0:print('checked',i,flush=True)
 assert len(maps)=={1:99,2:9726}[d] and len(un)=={1:39,2:0}[d]
 print('dimension',d,'orbits',len(maps),'not excluded',un,'maximum separator steps',st,'seconds',time.monotonic()-t,flush=True)
