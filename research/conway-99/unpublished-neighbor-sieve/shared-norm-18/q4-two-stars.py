"""Exact rank-36 Q4 two-star test, with H in conflict-cycle order."""
from itertools import combinations,product,permutations
from collections import Counter
import numpy as np
V=range(8);Z=range(11)
def bits(x):return [i for i in range(x.bit_length()) if x>>i&1]
masks=[x for x in range(256)if x.bit_count()>=2 and not(x&(x<<1))and not(x&1 and x&128)]
def trans(x,s,f):
 return sum(1<<((s+(1-2*f)*h)%8)for h in bits(x))
per=[[trans(x,s,f)for x in range(256)]for s,f in product(V,range(2))]
def incidence():
 d=[0]*8;pp=Counter();tab=[]
 def make(rem,lo):
  if not rem:
   if min(d)==4:
    t=tuple(sorted(tab))
    if all(t<=tuple(sorted(p[x]for x in t))for p in per):yield t
   return
  r=rem[0]
  for x in masks:
   if x<lo or x.bit_count()!=r:continue
   y=bits(x);pairs=list(combinations(y,2))
   if any(d[h]>=4 for h in y)or any(pp[k]>=2 for k in pairs):continue
   for h in y:d[h]+=1
   pp.update(pairs);tab.append(x)
   if min(d)+len(rem)-1>=4:yield from make(rem[1:],x+(r>2) if len(rem)>1 and rem[1]==r else 0)
   tab.pop();pp.subtract(pairs)
   for h in y:d[h]-=1
 for a in range(3):yield from make([4]*a+[3]*(10-2*a)+[2]*(1+a),0)
def forests(B):
 d=[x.bit_count()-2 for x in B];N=[set()for i in Z]
 def go(k):
  while k<11 and not d[k]:k+=1
  if k==11:
   for i in Z:
    for j in range(i):
     if (B[i]&B[j]).bit_count()+len(N[i]&N[j])>2-(j in N[i]):return
    for h in V:
     if sum(B[j]>>h&1 for j in N[i])>2-(B[i]>>h&1):return
    S={i};last=0
    while len(S)>last:last=len(S);S.update(set().union(*(N[v]for v in tuple(S))))
    if len(S)>4 or sum(len(N[v])for v in S)>=2*len(S):return
   yield tuple(tuple(sorted(x))for x in N);return
  good=[j for j in range(k+1,11) if d[j] and (B[k]&B[j]).bit_count()<=1]
  for J in combinations(good,d[k]):
   for j in J:d[j]-=1;N[k].add(j);N[j].add(k)
   d[k]-=len(J);yield from go(k+1);d[k]+=len(J)
   for j in J:d[j]+=1;N[k].remove(j);N[j].remove(k)
 yield from go(0)
# Reduced under the full D8 action, before embedding the cube, not a cube automorphism.
def B19(B,E):
 A=np.zeros((19,19),int)
 for i in Z:
  for j in E[i]:A[8+i,8+j]=1
  for h in bits(B[i]):A[8+i,h]=A[h,8+i]=1
 return A
# Products according to the two public cube portraits, in both cases H in circular order.
C=[(33153,17025,16932,6180,6168,9240,9282,33090),(33153,17025,16920,6168,6180,9252,9282,33090)]
def A35(old,t,shift):
 A=np.zeros((35,35),int);A[16:,16:]=old
 v=sorted(range(16),key=lambda x:x.bit_count()%2)
 for i,j in combinations(range(16),2):A[i,j]=A[j,i]=((v[i]^v[j]).bit_count()==1)
 for i in V:
  for j in bits(C[t][(i+shift)%8]):A[j,16+i]=A[16+i,j]=1
 return A
def catalog():
 S=list(incidence());assert len(S)==63
 F=[(B,E)for B in S for E in forests(B)]
 assert Counter(sum(x.bit_count()==4 for x in B)for B,E in F)=={0:2693,1:785,2:43}
 return F

def bwords(M):
 A=M[16:,16:];R=12*np.eye(35,dtype=int)-M-M@M+2;R0=R[16:,16:]
 hos=[tuple(L) for j in range(5)for L in combinations(range(8),j) if all(R0[k,l]>0 for k,l in combinations(L,2))]
 words=[]
 for L in hos:
  ok=[i for i in range(8,19)if all(R0[h,i]>0 for h in L)]
  for Z0 in combinations(ok,len(L)+1):
   W=L+Z0
   if any(R0[i,j]<=0 for i,j in combinations(Z0,2)):continue
   if any(sum(A[j,k] for k in W)>1 for j in W):continue
   words.append(W)
 return words,R
def candidates(M):
 W,R=bwords(M);B=np.zeros((len(W),19),np.int8)
 for i,ww in enumerate(W):B[i,list(ww)]=1
 bad=(B @ (R[16:,:16]==0).astype(np.int8))>0
 # Additional core matching or row common quotas y against each physical cube+h+z site.
 # A candidate is invalid if a true core site j sees too many of its known neighbors in y's support.
 W0=[]
 for p in range(8):
  for n in range(8,16):
   if R[p,n]==0:continue
   t=np.flatnonzero(~(bad[:,p]|bad[:,n]))
   D=np.zeros((len(t),35),np.int8);D[:,16:]=B[t];D[:,p]=D[:,n]=1
   ok=~np.any(D@M>2-D,axis=1)
   W0.append(D[ok])
 return np.vstack(W0),R
def hsets(M,h,cap=20000):
 W,R=bwords(M);R=R[16:,16:];B=M[16:,16:];W=[x for x in W if h in x]
 E0=set(i for i in range(19)if B[i,h])
 masks=[sum(1<<k for k in w)for w in W]
 cols=[sum(1<<j for j,x in enumerate(W)if i in x)for i in range(19)]
 bad=[sum(1<<j for j,x in enumerate(masks)if (x&ms).bit_count()>=3)for ms in masks]; tar=list(R[h]);stack=[];answer=[];nodes=0;allw=(1<<len(W))-1
 def dfs(pool):
  nonlocal nodes;nodes+=1
  if len(answer)>=cap:return
  if len(stack)==6:
   if any(tar):return
   # Known common-neighbor budgets of the old B after choosing these six.
   for i in range(19):
    for j in range(i):
     if sum(i in W[x]and j in W[x] for x in stack)>R[i,j]:return
   free=[j for j,v in enumerate(stack)if not(E0 & set(W[v]))]
   if len(free)%2:return
   def match(f,mates):
    if not f:answer.append((tuple(W[k]for k in stack),tuple(mates)));return
    i,*tail=f
    for t,j in enumerate(tail):
     if (masks[stack[i]]&masks[stack[j]]).bit_count()==1:
      match(tail[:t]+tail[t+1:],mates+[(i,j)])
   match(free,[]);return
  need=[(pool&cols[i],i)for i,d in enumerate(tar)if d]
  if any(c.bit_count()<tar[i]for c,i in need):return
  c,v=min(need,key=lambda q: __import__('math').comb(q[0].bit_count(),tar[q[1]]))
  def tr(c0,pool,t):
   if not t:dfs(pool);return
   c0&=pool
   while c0.bit_count()>=t and len(answer)<cap:
    ix=c0&-c0;c0-=ix;j=ix.bit_length()-1;pp=pool&~bad[j];good=True
    for k in W[j]:
     tar[k]-=1
     if not tar[k]:pp&=~cols[k]
     if tar[k]<0:good=False
    stack.append(j)
    if good:tr(c0,pp,t-1)
    stack.pop()
    for k in W[j]:tar[k]+=1
  tr(c,pool,tar[v])
 dfs(allw);return answer,nodes

def ff(A):
 A=np.asarray(A,dtype=np.int64).copy()%7;piv=[];det=1;r=0
 for j in range(A.shape[1]):
  if r==len(A):break
  a=np.flatnonzero(A[r:,j])
  if not len(a):continue
  k=r+a[0];det=det*(1 if k==r else -1)*int(A[k,j])%7;A[[k,r]]=A[[r,k]];A[r]=A[r]*pow(int(A[r,j]),-1,7)%7
  v=A[:,j].copy();v[r]=0;A=(A-v[:,None]*A[r])%7;piv.append(j);r+=1
 return A,piv,det
def prep(M,h):
 W,R=candidates(M);W=W[W[:,16+h]>0];G=3*np.eye(35,dtype=int)-M+4;_,I,_=ff(G);r=len(I);_,_,d=ff(G[np.ix_(I,I)])
 B,_,_=ff(np.column_stack([G[np.ix_(I,I)],np.eye(r,dtype=int)]));J=B[:,r:]
 T=(4-W[:,I])%7;C=T@J%7;Q=(T@C.T)%7;diag=(-Q.diagonal())%7
 D={};W0=W@M
 for i,v in enumerate(W):
  p=int(np.where(v[:8])[0][0]);n=int(np.where(v[8:16])[0][0])+8;word=tuple(np.flatnonzero(v[16:]))
  D.setdefault(word,[]).append((i,p,n))
 ps=np.flatnonzero(R[16+h,:8]);ns=np.flatnonzero(R[16+h,8:16])+8
 return (W,W0,Q,diag,D,ps,ns,36-r,3*pow(d,-1,7)%7)
def trytags(cfg,S,mates):
 W,W0,Q,diag,D,ps,ns,L,delta=cfg;nw=6
 CS=[D.get(tuple(x),[])for x in S]
 if any(not c for c in CS):return None
 # each slot has one distinct p and n. enumerate 6!^2 assignments by NumPy array expansion,
 # rejecting any with a repeated tag or incompatible mate as it arises.
 ord0=sorted(range(6),key=lambda k:len(CS[k]));CS=[CS[k]for k in ord0]
 lut={tuple(sorted((ord0.index(a),ord0.index(b))))for a,b in mates}
 # IDs' low and high tags are kept separately in arrays.
 u=np.zeros(1,np.int32);v=u.copy();Z=np.zeros((1,0),np.int32)
 for k,cs in enumerate(CS):
  ids=np.array([c[0]for c in cs],np.int32);p=1<<np.array([c[1]for c in cs]);n=1<<np.array([c[2]-8 for c in cs])
  ii,jj=np.where(((u[:,None]&p)==0)&((v[:,None]&n)==0))
  if not len(ii):return None
  Z=Z[ii];i=ids[jj];u=u[ii]|p[jj];v=v[ii]|n[jj]
  for k0 in range(k):
   if (k0,k) not in lut:continue
   # Each mate contributes a further old-site common neighbor to this Y site.
   x=Z[:,k0];keep=np.all(W0[i]+W[x]<=2-W[i],axis=1)&np.all(W0[x]+W[i]<=2-W[x],axis=1)
   Z=Z[keep];i=i[keep];u=u[keep];v=v[keep]
  Z=np.column_stack((Z,i));m=len(i)
  if not m:return None
  if k>=L:
   # Test necessary principal (L+1)-minors using true adjacency 3/4.
   for pair in combinations(range(k),L):
    T=Z[:,[*pair,k]];size=L+1
    U=4-Q[T[:,:,None],T[:,None,:]]
    order=[*pair,k]
    for j0,x in enumerate(order):
     U[:,j0,j0]=diag[T[:,j0]]
     for j1,y in enumerate(order[:j0]):
      if (y,x)in lut:U[:,j0,j1]-=1;U[:,j1,j0]-=1
    # use exact permutation determinants; small L capped in the probe.
    if size>5:break
    det=np.zeros(len(U),np.int64)
    for perm,sgn in DP[size]:det+=sgn*U[:,range(size),perm].prod(axis=1)
    ok=det%7==0;Z=Z[ok];u=u[ok];v=v[ok]
    if not len(Z):return None
 for z in Z:
  U=(4-Q[np.ix_(z,z)])%7;U[np.diag_indices(6)]=diag[z]
  for i,j in lut:U[i,j]-=1;U[j,i]-=1
  _,ix,_=ff(U)
  if len(ix)>L:continue
  if len(ix)==L and ff(U[np.ix_(ix,ix)])[2]*delta%7 not in (1,2,4):continue
  yield W[z], np.array([[int(tuple(sorted((i,j))) in lut)for j in range(6)]for i in range(6)])
 return None
DP={n:[(p,(-1)**sum(i>j for i,j in combinations(p,2)))for p in permutations(range(n))]for n in range(1,6)}

def second(M,h0,h1,A6,W6,W00):
 n=35;U=np.zeros((41,41),np.int64);U[:n,:n]=M;U[n:,:n]=W6;U[:n,n:]=W6.T;U[n:,n:]=A6
 G=3*np.eye(41,dtype=int)-U+4
 R=12*np.eye(41,dtype=int)+2-U-U@U
 if R.min()<0:return False
 _,ix,_=ff(G);r=len(ix)
 if r>36:return False
 if r<35:return True
 A,_,dd=ff(np.column_stack([G[np.ix_(ix,ix)],np.eye(r,dtype=int)]));inv=A[:,r:]
 _,_,det=ff(G[np.ix_(ix,ix)])
 if r==36 and det not in [3,5,6]:return False
 W00=W00[W00[:,16+h1]!=0]
 # y's true p and n are both distinct from h1's four support neighbors.
 zz=np.array(list(product(range(2),repeat=6)),np.int8)
 demand=R[16+h1].copy();assert demand[16+h1]==6
 zz=zz[np.all(zz<=demand[35:],axis=1)]
 W=np.column_stack((np.repeat(W00,len(zz),axis=0),np.tile(zz,(len(W00),1))))
 ok=~np.any((W>0)&(demand==0),axis=1);W=W[ok]
 W=W[np.all(W@U<=2-W,axis=1)]
 old=(4-W[:,ix])%7;pr=old@inv%7;ok=np.all((pr@G[ix,:]+W-4)%7==0,axis=1)
 dg=(-np.sum(old*pr,axis=1))%7
 if r==36:ok&=(dg==0)
 else:ok&=np.isin((dg*3*pow(det,-1,7))%7,[0,1,2,4])
 W=W[ok]
 # Pure necessity: each old site demand must be reachable from six *distinct* P labels.
 if not len(W):return False
 reach=np.zeros(41,int)
 for p in range(8):
  s=W[W[:,p]!=0]
  if len(s):reach+=s.max(axis=0)
 return min(reach-demand)>=0
from time import time
import sys
def fullrun():
 F=catalog();lo=int(sys.argv[1]);hi=int(sys.argv[2]);ao=int(sys.argv[3]);sels=(sys.argv[4] if len(sys.argv)>4 else '012345')
 T0=time();total=Counter();opens=[]
 for ix in range(lo,min(len(F),hi)):
  B,E=F[ix];a=sum(x.bit_count()==4 for x in B)
  if ao>=0 and a!=ao:continue
  m0=A35(B19(B,E),0,0);mv=1800;best=[];h0=-1;complete=False
  for h in range(8):
   a0,nn=hsets(m0,h,mv);total['unmarked calls']+=1
   if len(a0)<mv:
    mv=len(a0);best=a0;h0=h;complete=True
    if not mv:break
  if not complete:
   # Natural survivor if too many cases; never count a cutoff as exclusion.
   h0=0;best,nn=hsets(m0,h0,12000)
   if len(best)>=12000:opens.append((ix,'star cutoff'));continue
  for cf,(t,sh) in enumerate([(0,0),(0,1),(1,0),(1,1),(1,2),(1,3)]):
   if str(cf)not in sels:continue
   total['examined']+=1
   if not best:continue
   m=A35(B19(B,E),t,sh);w,r=candidates(m);cfg=prep(m,h0)
   h1=(h0+1)%8;live=None
   for ss,mt in best:
    for y,z in trytags(cfg,ss,mt):
     total['firsts']+=1
     if second(m,h0,h1,z,y,w):
      if second(m,h0,(h0+7)%8,z,y,w):live=1;break
    if live:break
   if live:opens.append((ix,cf,'incomplete outer'))
  if ix%5==0:print(ix,total,opens,round(time()-T0,1),flush=True)
 print('FINAL',lo,hi,ao,sels,total,opens,round(time()-T0,1),flush=True)
 if (lo,hi,ao,sels)==(3478,3521,2,'012345'):
  assert total['examined']==258 and not opens
if __name__=='__main__':fullrun()
