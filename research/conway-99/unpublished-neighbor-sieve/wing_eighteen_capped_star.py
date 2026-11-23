"""Single-star binary-adjacency / hyperbolic residual check on the 39 retained wing charts.
NumPy + Python, no numerical heuristics. Optional positional chart indices, 0 through 38.
Read the companion note for prerequisites; this checks a ten-vertex star, not a full graph.
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
import sys
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
 return rhs,Z,mat,ij,rows,gf,wing

b=reg36((0,3,2,1));rhs,Z,mat,ij,pr,gf,wing=b;cs=np.zeros((len(mat),36),np.int8);prs=np.array(pr)
for i,rrr in enumerate(mat):cs[i,prs[rrr].reshape(-1)]=1
def invmat(Q):
 n=len(Q);A=np.concatenate((np.array(Q,int),np.eye(n,dtype=int)),axis=1)%7
 for i in range(n):
  j=next(j for j in range(i,n) if A[j,i]);A[[i,j]]=A[[j,i]]
  A[i]=A[i]*pow(int(A[i,i]),-1,7)%7
  for j in range(n):
   if i!=j:A[j]=(A[j]-A[j,i]*A[i])%7
 return A[:,n:]

def piv(Q):
 A=Q.copy()%7;ids=[];r=0
 for j in range(A.shape[1]):
  h=np.flatnonzero(A[r:,j])
  if not len(h):continue
  h=h[0]+r;A[[h,r]]=A[[r,h]];A[r]=A[r]*pow(int(A[r,j]),-1,7)%7
  v=A[:,j].copy();v[r]=0;A=(A-v[:,None]*A[r])%7;ids.append(j);r+=1
 return ids
W=(np.array([[3*(i==j)-int(j in gf[i])+4 for j in range(36)] for i in range(36)]))%7;basis=piv(W);assert len(basis)==30
Cproj=invmat(W[np.ix_(basis,basis)]);big=(4-cs[:,basis])%7
def bits(x):
 return int.from_bytes(np.packbits(x,bitorder='little').tobytes(),'little')
def biter(n):
 while n:
  z=n&-n;yield z.bit_length()-1;n-=z
class Anchor:
 def __init__(self,M,i):
  gv=Y@M.T%7
  ids=np.where((np.all(gv[ij[:,0]]==Z[ij[:,1]],axis=1))&(cs[:,i]==1))[0]
  self.X=X=cs[ids].astype(int);self.i=i;self.U=Y[ij[ids,0]]
  self.P=(big[ids].astype(int)@Cproj@big[ids].T)%7;self.O=X@X.T
  self.q=np.array([0 if v==i else 2-int(v in gf[i])-len(gf[v]&gf[i])-int(wing[v]==wing[i]) for v in range(36)]);self.q[i]=10
  self.cap=[np.flatnonzero(X[:,j]) for j in sorted(gf[i]) if wing[j]!=wing[i]]
 def one(self,a,b,limit):
  X=self.X;i=self.i;P=self.P;O=self.O;S=self.U
  if O[a,b]>2:return 'over'
  non=np.cross(S[a],S[b])%7
  if not any(non):return self.dependent(a,b,limit)
  nb=next(k for k in range(3) if non[k]);Q=np.stack([S[a],S[b],np.eye(3,dtype=int)[nb]]);U=(S@invmat(Q))%7
  # Pair x_a,x_b cannot be adjacent to any other i-neighbor because they have near mates.
  ca,cb=(-4*P[a,a])%7,(-4*P[b,b])%7;raw=4-P[a,b]
  t0=(4-P[a,:]-U[:,0]*ca)%7;t1=(4-P[b,:]-U[:,0]*raw-U[:,1]*cb)%7
  d2=(-4*np.diag(P)-U[:,0]*t0-U[:,1]*t1)%7
  rr=self.q-X[a]-X[b];rr[i]=0
  if np.min(rr)<0:return 'pair-capacity'
  ok=np.all(X[:,np.array([j for j in range(36) if j!=i and rr[j]<=0],int)]==0,axis=1)&(O[a]<=2)&(O[b]<=2)&((U[:,2]!=0)|(d2==0))
  look=np.array([0,1,4,5,2,3,6]);idxs=np.flatnonzero(ok)
  src=np.repeat(idxs,np.where(U[idxs,2]!=0,1,7));I=U[src];H=np.stack([t0[src],t1[src],d2[src]*look[I[:,2]]%7],axis=1)
  nw=np.where(I[:,2]==0)[0];H[nw,2]=np.arange(len(nw))%7
  return self.go(src,I,H,rr,limit)
 def go(self,src,I,H,rr,limit):
  X=self.X;i=self.i;P=self.P;O=self.O
  N=len(src);FULL=(1<<N)-1
  mat=X[src];at=[bits(mat[:,j]!=0) for j in range(36)]
  ones=sum(1<<j for j in range(36) if rr[j]==1);twos=sum(1<<j for j in range(36) if rr[j]==2)
  csmap={}; edges={};adj={}; index=np.arange(N)
  def cache(l):
   if l not in csmap:
    j=src[l];q=(P[j,src]+I@H[l]+H@I[l])%7;ov=O[j,src];csmap[l]=bits((ov<=2)&((q==4)|((q==3)&(ov==1))))
    adj[l]=bits((q==3)&(ov==1));edges[l]=sum(1<<int(j) for j in np.nonzero(mat[l])[0] if j!=i)
  nodes=0
  def go(ones,twos,f,used,unmat):
   nonlocal nodes;nodes+=1
   if nodes>limit:return 2
   if not(ones|twos):return 0 if unmat else 1
   # Each available tuple after first two covers five positions, centered bin i omitted.
   b=None;n=10**9
   for j in biter(ones|twos):
    z=f&at[j];nn=z.bit_count();k=1+((twos>>j)&1)
    if nn<k:return 0
    score=nn
    if score<n:b,n=z,score
   while b:
    v=b&-b;b-=v;f&=~v;l=v.bit_length()-1;cache(l);e=edges[l];near=used&adj[l]
    if near.bit_count()>1 or near&~unmat:continue
    nb=f&csmap[l]
    for j in biter(e&ones):nb&=~at[j]
    if near:
     h=near.bit_length()-1;nb&=~(adj[h]|adj[l]);un=unmat^near
    else:un=unmat|v
    o=go((ones&~e)|(twos&e),twos&~e,nb,used|v,un)
    if o:return o
   return 0
  return go(ones,twos,FULL,0,0),nodes
 def dependent(self,a,b,limit):
  X=self.X;i=self.i;P=self.P;O=self.O;S=self.U
  assert np.any(S[a]) and np.any(S[b])
  # choose two independent coordinate rows to complete S[a] to a basis
  for u,v in combinations(range(3),2):
   Q=np.stack([S[a],np.eye(3,dtype=int)[u],np.eye(3,dtype=int)[v]])
   try:inv=invmat(Q);break
   except StopIteration:continue
  U=S@inv%7;lam=U[b,0];assert lam!=0 and not np.any(U[b,1:])
  aa=-4*P[a,a]%7;bb=(4-P[a,b]-lam*aa)%7
  if (2*lam*bb+P[b,b])%7:return 'dep-schur'
  rr=self.q-X[a]-X[b];rr[i]=0
  if np.min(rr)<0:return 'pair-capacity'
  ok=(np.all(X[:,np.array([j for j in range(36) if j!=i and rr[j]<=0],int)]==0,axis=1)&(O[a]<=2)&(O[b]<=2))
  t0=(4-P[a,:]-U[:,0]*aa)%7
  val=(4-P[b,:]-lam*t0-U[:,0]*bb)%7
  trg=(-4*np.diag(P)-U[:,0]*t0)%7
  inv7=np.array([0,1,4,5,2,3,6])
  cases=0
  for c,d in product(range(7),repeat=2):
   ind=np.flatnonzero(ok&((U[:,1]*c+U[:,2]*d-val)%7==0))
   if not len(ind) or np.any(X[ind].sum(0)<rr):continue
   nsol=np.where(np.any(U[ind,1:]!=0,axis=1),7,np.where(trg[ind]==0,49,0));src=np.repeat(ind,nsol)
   if not len(src):continue
   off=np.arange(len(src))-np.repeat(np.cumsum(nsol)-nsol,nsol);I=U[src]
   v1=np.where(I[:,2]!=0,off%7,np.where(I[:,1]!=0,trg[src]*inv7[I[:,1]]%7,off%7))
   v2=np.where(I[:,2]!=0,(trg[src]-I[:,1]*v1)*inv7[I[:,2]]%7,np.where(I[:,1]!=0,off%7,off//7))
   H=np.stack([t0[src],v1,v2],axis=1)
   z,n=self.go(src,I,H,rr,limit);cases+=n
   if z:return 'dep-pass' if z==1 else 'dep-unknown'
  return 'dep-fail'
def first(M):
 GV=Y@M.T%7;ids=np.flatnonzero(np.all(GV[ij[:,0]]==Z[ij[:,1]],axis=1))
 cand=[]
 for i in range(18,30):
  js=[j for j in gf[i] if wing[j]!=wing[i]]
  if js[0] in gf[js[1]]:continue
  ca=[ids[(cs[ids,i]==1)&(cs[ids,j]==1)] for j in js];v0=ca[0][np.any(cs[ca[0],30:36:2],axis=1)]
  cand.append((sum((cs[v0]@cs[ca[1]].T<=2).flat),i))
 return min(cand)
charts=[[0,1,2],[0,2,1],[0,4,2],[0,5,3],[1,0,0],[1,0,2],[1,0,3],[1,1,1],[1,2,0],[1,3,0],[1,3,2],[1,6,1],[2,0,0],[2,1,0],[2,3,0],[2,4,1],[3,0,0],[3,1,0],[3,2,0],[3,3,0],[3,3,1],[3,4,1],[4,1,0],[4,1,1],[4,5,1],[4,6,2],[5,0,1],[5,0,3],[5,1,0],[5,1,1],[5,3,0],[6,0,1],[6,1,1],[6,1,2],[6,2,0],[6,2,3],[6,3,0],[6,3,1],[6,5,2]]
def run(z):
 M=np.array([z]);cap,i=first(M);h=Anchor(M,i);ct=Counter();tot=0;big=0;cases=0
 for a in h.cap[0]:
  if not h.X[a,30:36:2].any():continue  # simultaneous swap of the two prism lines fixes every other component
  for b in h.cap[1]:
   v=h.one(a,b,20000)
   if isinstance(v,tuple):
    status,nodes=v;ct[status]+=1;tot+=nodes;big=max(big,nodes)
    if status:return dict(ct),int(i),big,('positive or unresolved',int(a),int(b))
   else:
    ct[v]+=1
    if v=='dep-pass' or v=='dep-unknown':return dict(ct),int(i),big,(v,int(a),int(b))
 assert sum(ct.values())-ct['over']==int(cap)
 return dict(ct),int(i),big,None
T=time.monotonic()
selected=list(map(int,sys.argv[1:])) if len(sys.argv)>1 else list(range(39))
assert len(charts)==39 and len({tuple(z) for z in charts})==39
for j in selected:
 z=charts[j];c,i,depth,v=run(z);assert v is None, ("positive or unresolved case",z,v);print('chart',j,z,i,c,'maxnodes',depth,'result',v,'elapsed',round(time.monotonic()-T,2),flush=True)
