import numpy as np
from itertools import product
from collections import defaultdict
import sys
P=65521
q, N = 7, 3
g = int(sys.argv[1])
c = [0, 31004, 56939, 56714, 21605, 26811, 9446]
u = [0, 33535, 27737, 49371, 29660, 42184, 53920]
d = [0, 49479, 17899, 54899, 51658, 36010, 62156]
e = [0, 62275, 54232, 35260, 8120, 5618, 16330]
dd = [0, 0, 0, 53566, 19866, 0, 0]
for j in (1,6):
 for v in (u,d,e):v[j]=v[j]*g%P
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
assert len(O)==609 and len(R)==27
pickle.dump((E,R,S),open('cub7_1_%d.pkl'%g,'wb'))
