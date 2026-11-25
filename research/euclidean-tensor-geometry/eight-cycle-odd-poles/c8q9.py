import numpy as np
from itertools import product
from collections import defaultdict
import sys
P=65521
nclass,N=int(sys.argv[1]),3
g=int(sys.argv[2]); g4=int(sys.argv[3]); choice=int(sys.argv[4])
patterns=[
[0,31004,56939,56714,21605,26811,9446],
[0,33535,27737,49371,29660,42184,53920],
[0,49479,17899,54899,51658,36010,62156],
[0,62275,54232,35260,8120,5618,16330],
[0,0,0,53566,19866,0,0]]
orig=list(zip(*patterns))
# map classes (-1 translates to 6, etc), mark 3; 4 a free class
fdata=[[17651,17353,17755,19478,0],[9972,8255,9931,6661,0]] if choice==0 else [[7809,4321,11223,7654,0],[2901,532,17333,8595,0]]
labs=[1,2,3,4] if nclass==4 else [3,4]
q=2*nclass+1
res=[list(orig[0])]+[None]*(q-1)
for j,cl in enumerate(labs,1):
 for sign in (1,-1):
  comps=list(orig[(sign*cl)%7]) if cl<4 else list(fdata[sign==-1])
  if cl in (1,4):
   scale=g if cl==1 else g4
   for l in (1,2,3):comps[l]=comps[l]*scale%P
  res[(sign*j)%q]=comps
c,u,d,e,dd=list(zip(*res))
A=[[] for i in range(q)]
for j in range(1,q):
 A[0].append((0,j,1,0,j))
 A[j].append((j,0,int(c[(-j)%q]),0,(-j)%q))
 A[j].append((j,j,int(d[j]),1,j))
 A[j].append((j,j,int(e[(-j)%q]),1,(-j)%q))
A[0].append((0,0,1,0,0))
# A0 tilt j -> 0
for j in range(1,q): A[j].append((j,0,int(u[j]),1,0))
for j in range(1,q): A[j].append((j,j,int(dd[j]),1,0))
def seqs():
 def go(start,i,z,coef,t,seq):
  if i==8:
   if z==start: yield coef,t,seq
  else:
   for _,x,b,k,j in A[z]:
    if b and t+k<=N:
     yield from go(start,i+1,x,coef*b%P,t+k,seq+(j,))
 for s in range(q):yield from go(s,0,s,1,0,())
def orbs():
 out=[]; lookup={}
 for w in product(range(q),repeat=4):
  orbit=[w]
  while (v:=orbit[-1][1:]+orbit[-1][:1])!=w:orbit.append(v)
  if min(orbit)==w and len(orbit)%2==0:
   for i,v in enumerate(orbit):lookup[v]=(len(out),(-1)**i)
   out.append(w)
 return out,lookup
O,L=orbs(); n=len(O)
M=[np.zeros((n,n),np.int64) for k in range(N+1)]
for b,t,seq in seqs():
 r=seq[::2]
 if r not in L:continue
 a,sg=L[r]
 if O[a]!=r:continue
 v=tuple((-i)%q for i in seq[1::2])
 if v not in L:continue
 j,sg=L[v];M[t][a,j]+=sg*b
M=[m%P for m in M]
def gauss(m):
 B=m.copy();rows=list(range(len(B)));cols=[];k=0
 for j in range(B.shape[1]):
  inds=np.flatnonzero(B[k:,j])
  if not len(inds):continue
  i=k+inds[0];B[[k,i]]=B[[i,k]];rows[k],rows[i]=rows[i],rows[k];cols.append(j)
  B[k]=B[k]*pow(int(B[k,j]),-1,P)%P
  f=B[:,j].copy();f[k]=0
  B=(B-f[:,None]*B[k,None,:])%P
  k+=1
 return rows[:k],cols,B
def blocks(O):
 G=defaultdict(list)
 for j,w in enumerate(O):G[tuple(sorted(w))].append(j)
 return G
def eliminate(M,O,max_order):
 G=blocks(O); row=[];col=[];Kr=[];Kc=[];BIN=[]
 for g,ids in G.items():
  H=M[0][np.ix_(ids,ids)]; i,j,B=gauss(H)
  row.extend(ids[k] for k in i);col.extend(ids[k] for k in j)
  Kr.extend(ids[k] for k in range(len(ids)) if k not in i)
  Kc.extend(ids[k] for k in range(len(ids)) if k not in j)
  S=H[np.ix_(i,j)]; r=len(i)
  _,_,bi=gauss(np.c_[S,np.eye(r,dtype=np.int64)])
  BIN.append(bi[:,r:])
 bin=np.zeros((len(row),len(row)),np.int64);h=0
 for bi in BIN:r=len(bi);bin[h:h+r,h:h+r]=bi;h+=r
 A=[m[np.ix_(row,col)] for m in M]
 B=[m[np.ix_(row,Kc)] for m in M]
 C=[m[np.ix_(Kr,col)] for m in M]
 D=[m[np.ix_(Kr,Kc)] for m in M]
 X=[];E=[]
 for k in range(max_order+1):
  X.append(bin@(B[k]-sum((A[j]@X[k-j])%P for j in range(1,k+1)))%P)
  E.append((D[k]-sum(C[j]@X[k-j] for j in range(k+1)))%P)
 print('initial n,rank, residual',len(O),len(row),len(Kr),flush=True)
 return E,[O[i] for i in Kr],[O[j] for j in Kc]
E,R,S=eliminate(M,O,N)
import pickle
pickle.dump((E,R,S),open('./c8q%d_%d_%d_%d.pkl'%(q,g,g4,choice),'wb'))
