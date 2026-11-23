"""Rank36 B12+B12+B12 exclusion, complete zero-current quotient replay. NumPy, exact F7 only."""
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
def table(pattern):
 E=[(i,j) for (i,j),n in M.items() if n];m0=len(E)
 real=np.array([[orient(w)[i//4] for i in range(12)] for w,k in pattern])
 ee=np.array(E);sz=np.array([[(ww[ee]==q).sum(1) for q in range(3)] for ww in real])
 a=np.array([[(k*(h[i]+h[j]))%7 for i,j in E] for _,k in pattern])
 q0=np.indices((m0,)*3,dtype=np.int16).reshape(3,-1);ii,jj,kk=q0
 k=(a[0,ii]+a[1,jj]+a[2,kk])%7==0
 for w in range(3):k &= sz[0,w,ii]+sz[1,w,jj]+sz[2,w,kk]==2
 IDs=q0[:,k]
 return E,real,IDs,None,None,None

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
def chart(op,c=0):
 from time import time
 E,real,ID,R,rhs,B=table(op);idx=[t for t in range(3) if t!=c];b=idx[0];ET=np.array(E);ar=(-np.array([sum(h[k] for k in e) for e in E],np.int16))%7
 use=np.where(ar[ID[c]]==0)[0];ID=ID[:,use];n=ID.shape[1]
 D0=np.zeros((12,12),np.int16)
 for i in range(12):D0[i,list(N[i])]=1
 D=np.kron(np.eye(3,dtype=np.int16),D0)
 G=(3*np.eye(36,dtype=np.int16)-D+4)%7;ss=invmat(G)[0];_,sd,inv=invmat(G[np.ix_(ss,ss)]);assert len(ss)==31 and sd in (3,5,6)
 W=np.zeros((n,36),np.int16)
 for j in range(3):W[np.arange(n)[:,None],12*j+ET[ID[j]]]=1
 p=(4-W[:,ss])%7;g=(p@inv%7)@p.T%7;nu=(-np.diag(g))%7;a=ar[ID[b]];wing=real.ravel()
 cap=2-D-D@D-(wing[:,None]==wing[None,:]).astype(np.int16);wordcap=2-W-W@D
 nmat=W@W.T;allow=(nmat<=2);allow1=(nmat<=1)&(((wordcap==0).astype(np.int16)@W.T)==0);allow1 &= allow1.T
 for j,k in zip(*np.where(np.triu(cap==1,1))):
  uu=np.where(W[:,j]&W[:,k])[0]
  if len(uu):allow[np.ix_(uu,uu)]=False
 # lifts h=(a,d,t), 2ad+t^2=nu. extra degenerate radical direction contributes nothing, so do not include.
 code=[(i,int(a[i]),d,t) for i in range(n) for t in range(7) for d in range(7) if (2*a[i]*d+t*t-nu[i])%7==0]
 U,aa,dd,tt=np.array(code,np.int16).T;kk=sorted(set(ID[c].tolist()));cc=[np.where(ID[c,U]==e)[0] for e in kk];assert len(cc)==10
 counts=list(map(len,cc));gs=[];bits={}
 for i in range(len(cc)):
  u=cc[i];gs.append((1<<len(u))-1)
  for j in range(len(cc)):
   if i==j:continue
   v=cc[j];J=(4-g[np.ix_(U[u],U[v])]-aa[u,None]*dd[v][None,:]-dd[u,None]*aa[v][None,:]-tt[u,None]*tt[v][None,:])%7
   ok=allow[np.ix_(U[u],U[v])]&((J==0)|((J==1)&allow1[np.ix_(U[u],U[v])]))
   bits[i,j]=[int.from_bytes(r.tobytes(),'little') for r in np.packbits(ok,axis=1,bitorder='little')]
 nodes=0;first=None
 def search(g,ix,anchor,path):
  nonlocal nodes,first
  nodes+=1
  if not ix:first=path;return 1
  j=min(ix,key=lambda j:g[j].bit_count())
  todo=g[j];rem=ix-{j}
  while todo:
   bt=todo&-todo;todo-=bt;r=bt.bit_length()-1;v=cc[j][r]
   # first nonzero-a choice can be normalized to t=0 by the common null translation t -> t+ka;
   # if earlier a=0 choices were pinned, their d moves with k * t, so require first decision only.
   if not path and aa[v] and tt[v]:continue
   ng=g.copy()
   for i in rem:
    ng[i] &= bits[j,i][r]
    if not ng[i]:break
   else:
    ans=search(ng,rem,anchor or aa[v]!=0,path+[int(v)])
    if ans:return ans
  return 0
 out=search(gs,set(range(10)),False,[])
 return n,counts,out,nodes,first

if __name__=='__main__':
 assert len(patterns)==14
 records=[]
 for j,pattern in enumerate(patterns):
  n,sizes,found,nodes,ex=chart(pattern,0);assert not found,(pattern,ex)
  records.append(nodes);print(j,pattern,n,nodes)
 assert records==[4753,899,899,5129,14881,20045,899,20045,5129,14881,20521,23303,25059,23303]
 print('All fourteen B+B+B orientation/current charts excluded.')
