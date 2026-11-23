"""Rank-36 B12 plus two unit twelve-site components: exact line-quotient replay."""
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

"""Classify twelve-site components and verify two integer infeasibility certificates."""
from collections import Counter
from itertools import combinations, permutations, product


MATES = ((1,0,3,2),(2,3,0,1),(3,2,1,0))
IDENTITY = (0,1,2,3)
CERTIFICATES = {
    (MATES[0], MATES[0], MATES[0], (0,2,1,3)): {
        (0,9): (-1,-1,-1,1,-1,-1,1,1,0,-1,-1,1),
        (1,5): (-1,0,-1,1,-1,0,1,1,-1,-1,-1,1),
        (1,8): (0,-1,-1,1,-1,-1,1,1,-1,-1,-1,1),
        (2,10): (2,0,-2,-2,2,2,0,-2,2,0,-2,-2),
        (5,9): (-1,-1,-1,1,-1,0,1,1,-1,0,-1,1),
    },
    (MATES[0], MATES[0], MATES[1], IDENTITY): {
        (1,8): (0,-1,1,1,-1,-1,1,1,-1,-1,0,0),
        (2,11): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (3,10): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (5,8): (-1,-1,1,1,0,-1,1,1,-1,-1,0,0),
        (6,11): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (7,10): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (8,9): (-1,-1,1,1,-1,-1,1,1,-1,-1,0,0),
    },
}


def typegraph(p, q, r, return_map):
    graph = [set() for _ in range(12)]
    for i in range(4):
        for a,b in ((i,p[i]),(4+i,4+q[i]),(8+i,8+r[i]),
                    (i,4+i),(4+i,8+i),(8+i,return_map[i])):
            graph[a].add(b)
            graph[b].add(a)
    return graph


def connected(graph):
    reached = {0}
    pending = [0]
    while pending:
        new = graph[pending.pop()] - reached
        reached.update(new)
        pending.extend(new)
    return len(reached) == 12


def multiplicities(graph):
    return {(a,b): 2 - int(b in graph[a]) - len(graph[a] & graph[b]) - int(a//4 == b//4)
            for a,b in combinations(range(12),2)}


def code(parameters, ordered_wings=False):
    graph = typegraph(*parameters)
    keys = []
    for a,b,c in ((0,1,2),) if ordered_wings else permutations(range(3)):
        for order in permutations(range(4*a,4*a+4)):
            second = [next(j for j in graph[i] if j//4 == b) for i in order]
            third = [next(j for j in graph[i] if j//4 == c) for i in second]
            labels = list(order) + second + third
            keys.append(tuple(int(labels[j] in graph[labels[i]]) for i,j in combinations(range(12),2)))
    return min(keys)



def generic(components,wings,mode,limit=30000):
 # each components list 3 explicit ordered cubic arrays, first B; unique middle B1 physical wing 1.
 DE=[];Eall=[];Rall=[];dsz=[];Ns=0
 for NN,perm in zip(components,wings):
  d=np.array([[int(j in NN[i]) for j in range(len(NN))] for i in range(len(NN))],np.int16)
  ww=np.array([perm[i//4] for i in range(12)]);r=2-d-d@d-(ww[:,None]==ww[None,:])
  es=np.array([(i,j) for i,j in combinations(range(12),2) if r[i,j]>0]);de=r.copy()
  DE.append(d);Eall.append(es+Ns);Rall.append(ww);dsz.append(np.array([(ww[es]==q).sum(1) for q in range(3)]));Ns+=len(d)
 assert Ns==36
 l=[len(e) for e in Eall];ID=np.indices(l,dtype=np.int16).reshape(3,-1)
 loc=Eall[0];ar=(-np.array([sum(h[k] for k in x) for x in loc],np.int16))%7
 use=(ar[ID[0]]==0)
 for w in range(3):use &= (sum(dsz[idx][w,ID[idx]] for idx in range(3))==2)
 ID=ID[:,use];n=ID.shape[1];ww=np.concatenate(Rall)
 D=np.zeros((36,36),np.int16)
 for i in range(3):D[12*i:12*i+12,12*i:12*i+12]=DE[i]
 G=(3*np.eye(36,dtype=np.int16)-D+4)%7;ss=invmat(G)[0];_,sd,inv=invmat(G[np.ix_(ss,ss)]);assert len(ss)=={'BBU':32,'BUU':33}[mode]
 W=np.zeros((n,36),np.int16)
 for j in range(3):W[np.arange(n)[:,None],Eall[j][ID[j]]]=1
 p=(4-W[:,ss])%7;pr=p@inv%7;nu=(-(p*pr).sum(1))%7
 cap=2-D-D@D-(ww[:,None]==ww[None,:]).astype(np.int16);wordcap=2-W-W@D
 if mode=='BBU':
  a=(-np.array([sum(h[k-12] for k in e) for e in Eall[1]],np.int16))[ID[1]]%7
  code=[(i,int(a[i]),d) for i in range(n) for d in range(7) if 2*a[i]*d%7==nu[i]]
 else:
  eps=1 if sd in (1,2,4) else 3 # full nonsquare / W sign / hyperbolic minus = sign W
  code=[(i,0,t) for i in range(n) for t in range(7) if eps*t*t%7==nu[i]]
 U,aa,dd=np.array(code,np.int16).T;kk=sorted(set(ID[0].tolist()));cc=[np.where(ID[0,U]==e)[0] for e in kk];assert len(cc)==10
 counts=list(map(len,cc));gs=[];bits={};key=[set(np.where(r)[0]) for r in W] # retained words distinct
 cap1=[(i,j) for i,j in combinations(range(36),2) if cap[i,j]==1]
 for i in range(10):
  u=cc[i];gs.append((1<<len(u))-1)
  for j in range(i):
   v=cc[j];au=U[u];av=U[v]
   H=(aa[u,None]*dd[v][None,:]+dd[u,None]*aa[v][None,:]) if mode=='BBU' else eps*dd[u,None]*dd[v][None,:]
   J=(4-pr[au]@p[av].T-H)%7;near=W[au]@W[av].T
   ok=(J<=1)&(near<=2-J)
   ok &= ((J==0)|((((wordcap[au]==0).astype(np.int16)@W[av].T)==0)&((W[au]@(wordcap[av]==0).T.astype(np.int16))==0)))
   for l,k in cap1:
    iu=np.where(W[au,l]&W[au,k])[0];iv=np.where(W[av,l]&W[av,k])[0]
    if len(iu)*len(iv):ok[np.ix_(iu,iv)]=False
   bits[i,j]=[int.from_bytes(r.tobytes(),'little') for r in np.packbits(ok,axis=1,bitorder='little')]
   bits[j,i]=[int.from_bytes(r.tobytes(),'little') for r in np.packbits(ok.T,axis=1,bitorder='little')]
 nodes=0
 def search(g,ix):
  nonlocal nodes
  nodes+=1
  if limit and nodes>limit:return -1
  if not ix:return 1
  j=min(ix,key=lambda j:g[j].bit_count());todo=g[j];rem=ix-{j}
  while todo:
   bt=todo&-todo;todo-=bt;r=bt.bit_length()-1;ng=g.copy()
   for i in rem:
    ng[i] &= bits[j,i][r]
    if not ng[i]:break
   else:
    ans=search(ng,rem)
    if ans:return ans
  return 0
 return search(gs,set(range(10))),nodes,counts
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

def make():
 U={};seen=set()
 for q,r,f in product(MATES,MATES,permutations(range(4))):
  pars=MATES[0],q,r,f;G=typegraph(*pars)
  if not connected(G) or min(multiplicities(G).values())<0:continue
  c=code(pars)
  if c in seen:continue
  seen.add(c)
  if c in {code(t) for t in CERTIFICATES}:continue
  L=3*np.eye(12,dtype=np.int16)-np.array([[int(j in G[i]) for j in range(12)] for i in range(12)],np.int16)
  pi,dt,_=invmat(L[:-1,:-1])
  if len(pi)==11:U[pars]=dt
 return U

def ordkey(G,perm):
 u,v,w=[perm.index(k) for k in range(3)];keys=[]
 for A in permutations(range(4*u,4*u+4)):
  B=[next(j for j in G[i] if j//4==v) for i in A];C=[next(j for j in G[i] if j//4==w) for i in B];sites=list(A)+B+C
  keys.append(tuple(int(sites[j] in G[sites[i]]) for i,j in combinations(range(12),2)))
 return min(keys)
def ordered():
 uns=make();cs={}
 for p,dt in uns.items():
  G=typegraph(*p)
  for w in permutations(range(3)):
   k=ordkey(G,w);cs.setdefault(k,(p,w,dt))
 return list(cs.values())
if __name__=='__main__':
 import time;tic=time.time();U=ordered()
 assert len(U)==25;print('relative unit charts',len(U),Counter(x[2] for x in U),flush=True)
 c=Counter();maxn=0;rem=[]
 for i,(p,w,dt) in enumerate(U):
  for j in range(i+1):
   q,z,dq=U[j];done,nd,cs=generic([N,typegraph(*p),typegraph(*q)],[(0,1,2),w,z],'BUU',None)
   c[done]+=1;maxn=max(maxn,nd)
   assert not done,(i,j,done,nd)
  if i%4==0 or i+1==len(U):print('completed first',i+1,c,maxn,'remaining',rem[:6],round(time.time()-tic,1),flush=True)

 assert c=={0:325} and maxn==62777
