"""Rank-36 A12 plus two B12 components: exact orthogonal-quotient replay."""
from itertools import combinations
from collections import Counter
from fractions import Fraction

def rank(A):
 A=[[Fraction(x) for x in row] for row in A];r=0
 for j in range(len(A[0])):
  i=next((i for i in range(r,len(A)) if A[i][j]),None)
  if i is None:continue
  A[i],A[r]=A[r],A[i]
  for i in range(r+1,len(A)):
   q=A[i][j]/A[r][j];A[i]=[a-q*b for a,b in zip(A[i],A[r])]
  r+=1
 return r
P=(1,0,3,2);Q=(2,3,0,1);f=(0,3,2,1)
N=[set() for _ in range(12)]
for i in range(4):
 for a,b in [(i,P[i]),(4+i,4+Q[i]),(8+i,8+P[i]),(i,4+i),(4+i,8+i),(8+i,f[i])]:N[a].add(b);N[b].add(a)
h=(2,1,5,6,0,0,0,0,5,6,2,1)
assert sum(h)%7==0 and all((3*h[i]-sum(h[j] for j in N[i]))%7==0 for i in range(12))
M={(i,j):2-int(j in N[i])-len(N[i]&N[j])-int(i//4==j//4) for i,j in combinations(range(12),2)}

from itertools import permutations
import numpy as np
W=np.arange(12)//4
aut=set()
for g in permutations(range(3)):
 for p in permutations(range(4)):
  s=[None]*12
  for i,pi in enumerate(p):
   s[i]=g[0]*4+pi
   for w in (1,2):
    j=next(v for v in N[i] if v//4==w);s[j]=next(v for v in N[s[i]] if v//4==g[w])
  if set(s)!=set(range(12)) or any(s[j] not in N[s[i]] for i in range(12) for j in N[i]):continue
  st=next(t for t in range(1,7) if all((h[s[i]]-t*h[i])%7==0 for i in range(12)))
  aut.add((g,st))
assert aut=={((0,1,2),1),((0,1,2),6),((2,1,0),1),((2,1,0),6)}

from collections import Counter
from itertools import product,combinations_with_replacement

mag=lambda k:min(k%7,(-k)%7)
def red(p):
 return min(tuple(sorted((g[w],mag(k*s)) for w,k in p)) for g in permutations(range(3)) for s in (1,2,3))
patterns=sorted(set(red(p) for p in combinations_with_replacement(product(range(3),range(1,4)),3)))
# local middle wing maps to w; remaining two can be ordered since aut includes outer exchange.
def orient(w):return [next(t for t in range(3) if t!=w),w,next(t for t in reversed(range(3)) if t!=w)]
inv7=np.array([0,1,4,5,2,3,6],np.int16)
def invmat(A):
 A=np.array(A,np.int16)%7;n,m=A.shape;B=np.eye(n,dtype=np.int16);piv=[];det=1
 for j in range(m):
  i=len(piv);ns=np.where(A[i:,j]!=0)[0]
  if not len(ns):continue
  ij=i+ns[0];piv.append(j);det=det*int(A[ij,j])*(-1 if ij!=i else 1)%7
  for X in (A,B):
   X[[i,ij]]=X[[ij,i]]
  s=inv7[A[i,j]]
  for X in (A,B):X[i]=X[i]*s%7
  coeff=A[:,j,None].copy();coeff[i]=0
  for X in (A,B):X[:]=(X-coeff*X[i])%7
 return piv,det,B

A0=np.array((1,4,3,6,6,4,3,1,0,0,0,0));A1=np.array((1,4,3,6,0,0,0,0,6,3,4,1))
AN=[set() for _ in range(12)]
for i in range(4):
 for a,b in ((i,(1,0,3,2)[i]),(4+i,4+(2,3,0,1)[i]),(8+i,8+(1,0,3,2)[i]),(i,4+i),(4+i,8+i),(8+i,(0,2,1,3)[i])):AN[a].add(b);AN[b].add(a)
assert all(sum(v)%7==0 and all((3*v[i]-sum(v[j] for j in AN[i]))%7==0 for i in range(12)) for v in (A0,A1))
Ds=[np.array([[int(t in ns[i]) for t in range(12)] for i in range(12)],np.int16) for ns in (AN,N,N)];D=np.zeros((36,36),np.int16)
for i in range(3):D[12*i:12*i+12,12*i:12*i+12]=Ds[i]
G=(3*np.eye(36,dtype=np.int16)-D+4)%7;I=invmat(G)[0];_,sd,inv=invmat(G[np.ix_(I,I)]);assert len(I)==30
E=[np.array([e for e in combinations(range(12),2) if (2-y-y@y-(np.arange(12)[:,None]//4==np.arange(12)[None,:]//4))[e]>0]) for y in Ds]
def needchart(line,left,right,mx):
 phi=(line*A0+A1)%7 if line<7 else A0.copy();psi=A0 if line<7 else A1
 wg=(tuple(range(3)),orient(left[0]),orient(right[0]));real=np.array([[s[i//4] for i in range(12)] for s in wg]);wc=real.ravel()
 a0=[(phi[E[0]].sum(1))%7,(-psi[E[0]].sum(1))%7]
 a1=(-np.array(h)[E[1]].sum(1))%7
 ew=[np.array([(real[j,e]==k).sum(1) for k in range(3)]) for j,e in enumerate(E)]
 ID=np.indices([len(e) for e in E],dtype=np.int16).reshape(3,-1);u,v,w=ID
 use=(a0[0][u]==0)&((left[1]*a1[v]+right[1]*a1[w])%7==0)
 for k in range(3):use&=(ew[0][k,u]+ew[1][k,v]+ew[2][k,w])==2
 ID=ID[:,use];n=ID.shape[1];a=np.column_stack((a0[1][ID[0]],a1[ID[1]])).astype(np.int16)
 W=np.zeros((n,36),np.int16)
 for j in range(3):W[np.arange(n)[:,None],12*j+E[j][ID[j]]]=1
 p=(4-W[:,I])%7;g=(p@inv%7)@p.T%7;nu=(-np.diag(g))%7
 cap=2-D-D@D-(wc[:,None]==wc[None,:]);need=2-W-W@D;near=W@W.T
 allow=(near<=2);allow1=(near<=1)&((W@(need==0).astype(np.int16).T)==0);allow1 &= allow1.T
 for i,j in zip(*np.where(np.triu(cap==1,1))):
  ix=np.where(W[:,i]&W[:,j])[0];allow[np.ix_(ix,ix)]=False
 d0=np.array(list(product(range(7),repeat=2)),np.int16);U,K=np.where((2*a@d0.T)%7==nu[:,None]);kk=sorted(set(ID[0].tolist()));c=[np.where(ID[0,U]==e)[0] for e in kk];aa=a[U];dd=d0[K]
 assert len(c) in (10,12,14)
 gs=[(1<<len(z))-1 for z in c];bb={}
 for i,u in enumerate(c):
  for j,v in enumerate(c[:i]):
   J=(4-g[np.ix_(U[u],U[v])]-aa[u]@dd[v].T-dd[u]@aa[v].T)%7
   ok=allow[np.ix_(U[u],U[v])]&((J==0)|((J==1)&allow1[np.ix_(U[u],U[v])]))
   bb[i,j]=[int.from_bytes(r.tobytes(),'little') for r in np.packbits(ok,axis=1,bitorder='little')]
   bb[j,i]=[int.from_bytes(r.tobytes(),'little') for r in np.packbits(ok.T,axis=1,bitorder='little')]
 # Gauge d -> d + s J a, skew J. If a0 !=0 set d1=0; if a0=0 !=a1 set d0=0. If a=0 no restriction.
 anchor=[sum(1<<k for k,u in enumerate(us) if (aa[u,0]!=0 and dd[u,1]==0) or (aa[u,0]==0 and (aa[u,1]==0 or dd[u,0]==0))) for us in c]
 nodes=0
 def go(rem,g,first):
  nonlocal nodes
  nodes+=1
  if mx and nodes>mx:return -1
  if not rem:return 1
  t=min(rem,key=lambda u:g[u].bit_count());R=rem-{t};z=g[t]&(anchor[t] if first else -1)
  while z:
   bt=z&-z;z-=bt;v=bt.bit_length()-1;ng=g.copy()
   for j in R:
    ng[j] &= bb[t,j][v]
    if not ng[j]:break
   else:
    h=go(R,ng,False)
    if h:return h
  return 0
 return go(set(range(len(c))),gs,True),nodes
if __name__=='__main__':
 import time;tic=time.time();c=Counter();maxn=0
 for line in range(8):
  for l,r in combinations_with_replacement(product(range(3),range(1,4)),2):
   ans,n=needchart(line,l,r,None);c[ans]+=1;maxn=max(maxn,n)
   assert not ans,(line,l,r,ans,n)
  print('line',line,c,maxn,round(time.time()-tic,1),flush=True)

 assert c=={0:360} and maxn==10403
