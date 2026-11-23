"""Fixed-Fano two-star test. No solver or randomized choice. Requires numpy and sympy."""
import numpy as np, sympy as sp
from sympy.polys.matrices import DomainMatrix as DM
F=sp.GF(7);Q=lambda m:DM.from_Matrix(sp.Matrix(m)).convert_to(F)
AM=sp.zeros(14,14);p=0
for a in range(7):
 for b in range(7):
  AM[a,7+b]=AM[7+b,a]=((a+1)&(b+1)).bit_count()%2
sig=[j for j in range(7) if AM[p,7+j]];dou=[j for j in range(7) if not AM[p,7+j]]
tags=sig+sum(([v,v]for v in dou),[])
# actual matching between H(p) in the distinguished neighborhood;
# each double pair sends one of its copies to each other pair. All signs negative around the triangle.
pairs=[(4,7),(6,9),(8,5)]
from itertools import combinations,product
from collections import Counter
from math import comb
N=np.array([(int(i>=4),*(int(i==4+2*j)-int(i==5+2*j) for j in range(3))) for i in range(4,10)])
H=np.array([[4,0,0,0],[0,5,3,3],[0,3,5,3],[0,3,3,5]])
I=set((a-4,b-4) if a<b else (b-4,a-4) for a,b in pairs)|{(0,1),(2,3),(4,5)}
edges=[k for k in combinations(range(6),2) if k not in I]
Eall=np.array([np.outer(N[i],N[j])+np.outer(N[j],N[i])for i,j in edges])
keep=[];st=Counter()
for bits in product(range(2),repeat=9):
 D=np.array(bits)@np.array([np.eye(6,dtype=int)[i]+np.eye(6,dtype=int)[j]for i,j in edges])
 if max(D)>3:continue
 st['degs']+=1
 if sum(D)<6:continue # six degree3 dbls can accept twelve single incidence only; true lower 18-12=6
 st['capac']+=1
 M=(H-(np.array(bits)@Eall.reshape(9,-1)).reshape(4,4))%7
 r=Q(M.tolist()).rank()
 if r>3:continue
 st['rank']+=1
 if r==3:
  p=Q(M.tolist()).rref()[1];v=int(sp.Matrix(M.tolist())[p,p].det())%7
  if v not in [1,2,4]:continue
 st['type']+=1
 keep.append((bits,r,int(sum(D)//2),tuple(D)))
from itertools import permutations
# Binary Fano collineations of P-points taking p to p (indices bitvectors 1..7) and preserving dot with lines
def mob(P,i):
 return (P[0] if i&1 else 0)^(P[1] if i&2 else 0)^(P[2] if i&4 else 0)
group=[]
for Sx in permutations(range(2,8),2):
 M=(1,)+Sx;G0=[mob(M,i) for i in range(1,8)]
 if len(set(G0))<7:continue
 ng=[next((k for k in range(1,8) if all(((k&i).bit_count()-(a&j).bit_count())%2==0 for i,j in zip(G0,range(1,8)))),None) for a in range(1,8)]
 if None in ng:continue
 pm={i:sig.index(ng[t]-1) for i,t in enumerate(sig)}
 dp=[dou.index(ng[t]-1) for t in dou]
 for z in product([0,1],repeat=3):
  per=[pm[k] for k in range(4)]+[4+2*dp[k//2]+(k%2^z[k//2]) for k in range(6)]
  if {tuple(sorted((per[i],per[j])))for i,j in pairs}=={tuple(sorted((i,j)))for i,j in pairs}:break
 else:raise AssertionError
 group.append(per)
assert len({tuple(z) for z in group})==24 and len(keep)==32
def to_str(G):return tuple(sorted(tuple(sorted(e)) for e in G))
allpair=list(combinations(range(4),2));BY=Counter();reps=[]
for bits,r,ni,Dd in keep:
 D0set={(a+4,b+4) for take,(a,b) in zip(bits,edges) if take}
 smal=[q for q in group if to_str([(q[i],q[j])for i,j in D0set])==to_str(D0set)]
 if to_str(D0set)!=min(to_str([(q[i],q[j])for i,j in D0set])for q in group):continue
 for inn in combinations(allpair,ni-3):
  rem0=[3-sum(i in ab for ab in inn)for i in range(4)]
  proc=sorted(range(6),key=lambda j:abs(3-Dd[j]-2),reverse=True)
  def rec(j,rem,D):
   if j==len(proc):
    if any(rem):return
    A=to_str([*D0set,*inn,*D]);BY['label']+=1
    if A==min(to_str([(q[i],q[k])for i,k in A])for q in smal):reps.append(A);BY[ni]+=1
    return
   k=proc[j];c=3-Dd[k]
   for subset in combinations([i for i in range(4)if rem[i]],c):
    re=[r-(i in subset)for i,r in enumerate(rem)];rec(j+1,re,D+[(i,k+4) for i in subset])
  rec(0,rem0,[])
assert [BY[n] for n in (4,5,6,9)]==[1344,2211,136,1] and len(reps)==3692
print('cubic orbits', [BY[n] for n in (4,5,6,9)],flush=True)
from functools import lru_cache
from itertools import combinations
from time import time
@lru_cache(None)
def baseW(q,n,h):
 Z=np.zeros((455,39),dtype=np.int16)
 for i,z in enumerate(combinations(range(15),3)):Z[i,np.array(z)+14]=1
 Z[:,q]=Z[:,7+n]=1
 for j in h:Z[:,29+j]=1
 return Z
def rrefg(A):
 A=np.array(A%7,dtype=np.int16);r=0;p=[]
 for j in range(A.shape[1]):
  rr=np.where(A[r:,j])[0]
  if len(rr)==0:continue
  k=r+rr[0];A[[r,k]]=A[[k,r]];A[r]=A[r]*pow(int(A[r,j]),-1,7)%7
  v=A[:,j].copy();v[r]=0;A=(A-v[:,None]*A[[r]])%7;p.append(j);r+=1
  if r==len(A):break
 return p,A
def makesource(D):
 A=np.zeros((39,39),dtype=np.int16);A[:14,:14]=np.array(AM.tolist(),dtype=np.int16)
 for j,n in enumerate(tags):A[0,29+j]=A[29+j,0]=A[7+n,29+j]=A[29+j,7+n]=1
 for j,k in pairs:A[29+j,29+k]=A[29+k,29+j]=1
 for z,(i,j) in enumerate(D,14):
  for k in [i,j]:A[z,29+k]=A[29+k,z]=1
 G=np.zeros((40,40),dtype=np.int16);G[:39,:39]=3*np.eye(39,dtype=np.int16)-A+4
 G[39,39]=2;G[39,:7]=G[:7,39]=1;G[39,7:14]=G[7:14,39]=-1
 I,_=rrefg(G);assert len(I)==36
 P,B=rrefg(np.column_stack([G[np.ix_(I,I)],np.eye(36,dtype=np.int16)]));assert P==list(range(36))
 V=B[:,36:];J=[j for j in range(40) if j not in I]
 ext=V@G[np.ix_(I,J)]%7
 ca=A.T@A
 Ypairs=[(i,j)for i,j in combinations(range(10),2) if A[29+i,29+j]==0 and ca[29+i,29+j]==1]
 assert len(Ypairs)==24
 return A,I,V,J,ext,Ypairs
def stars(src,q):
 A,I,V,J,T,Ypairs=src
 rows=[];modes=[]
 for n in range(7):
  hs=[(a,)for a in range(10)] if AM[0,7+n] else Ypairs
  for h in hs:
   C=baseW(q,n,h)
   pars=4-C
   W=np.column_stack([pars,np.zeros(455,dtype=np.int16)]);X=W[:,I]
   pos=np.where(np.all((X@T-W[:,J])%7==0,axis=1))[0];X=X[pos]
   Y=X@V%7
   so=np.where((np.einsum('ij,ij->i',X,Y)%7==0))[0];pos=pos[so];X=X[so];Y=Y[so];R=C[pos]
   use=np.all(R@A+R<=2,axis=1)
   for v,w,r in zip(X[use],Y[use],R[use]):rows.append((v,w,r));modes.append(n)
 if any(modes.count(n)<2-int(AM[q,7+n]) for n in range(7)):return None
 X=np.array([v for v,w,r in rows],dtype=np.int16);Y=np.array([w for v,w,r in rows],dtype=np.int16);C=np.array([r for v,w,r in rows],dtype=np.int16)
 mo=np.array(modes);pr=Y@X.T%7;st=C@C.T
 single=np.array([int(AM[q,7+n])for n in mo],dtype=bool)
 ma=((pr==4)&(st<=2))|((pr==3)&(st<=1)&(mo[:,None]!=mo[None,:])&(~single[:,None])&(~single[None,:]))
 np.fill_diagonal(ma,False)
 return mo,C,ma
def packed(v):
 return int.from_bytes(np.packbits(np.asarray(v,dtype=np.uint8),bitorder='little').tobytes(),'little')
def checkstar(src,q,lim=100000):
 dat=stars(src,q)
 if dat is None:return False,0,0
 mo,C,ma=dat
 B=[packed(row) for row in ma]
 # Demand 2−A(q,n) sites of each negative label. Each of fifteen Z points must appear twice (all common neighbors of q,z are in this star).
 cov=np.hstack([np.stack([mo==n for n in range(7)],axis=1),C[:,14:29]])
 capinit=[2-int(AM[q,7+n])for n in range(7)]+[2]*15
 cols=[packed(row) for row in cov.T]
 supp=[np.flatnonzero(row).tolist() for row in cov]
 nodes=0
 def dfs(pool,needs):
  nonlocal nodes
  nodes+=1
  if nodes>lim:return None
  if not any(needs):return True
  best=None;score=None
  for j,d in enumerate(needs):
   if d<=0:continue
   p=pool&cols[j];n=p.bit_count()
   if n<d:return False
   val=comb(n,d)
   if score==None or val<score:score,best=val,(j,p)
  j,p=best
  while p:
   k=p&-p;pool^=k;p^=k;i=k.bit_length()-1
   pp=pool&B[i];nn=needs.copy()
   for z in supp[i]:
    nn[z]-=1
    if nn[z]==0:pp&=~cols[z]
   ok=dfs(pp,nn)
   if ok is not False:return ok
  return False
 return dfs((1<<len(mo))-1,capinit),len(mo),nodes
def scan(reps,off=0,end=None):
 start=time();stat=Counter();live=[];peak=0;nst=0
 for kk,D in enumerate(reps[off:end],off):
  sc=makesource(D);hit=False
  for q in range(1,7):
   ok,n,nodes=checkstar(sc,q);peak=max(peak,nodes);nst+=nodes
   if ok is False:stat[q]+=1;hit=True;break
  if not hit:live.append(kk)
  if (kk-off+1)%500==0:print('checkpoint',kk+1,dict(stat),len(live),peak,round(time()-start,2),flush=True)
 print('done',off,end,len(reps),dict(stat),len(live),live,peak,nst,round(time()-start,2),flush=True)
 assert not live, live

scan(reps)
