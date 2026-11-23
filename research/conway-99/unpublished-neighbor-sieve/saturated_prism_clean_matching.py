"""Rank-36 saturated-axis peripheral matching theorem. Exact NumPy integer replay.
No assumption about clean edges among the six required new signed-parent rows.
"""
import numpy as np
from itertools import permutations, combinations, product, combinations_with_replacement
from collections import Counter
W=np.array(sorted(set(permutations((0,0,1,1,2,2)))),int)
T=(2*W[:,None,:]+np.array(list(product(range(2),repeat=6)))[None,:,:]).reshape(-1,6)
Xid={tuple(r):i for i,r in enumerate(T)};pairs=list(combinations(range(6),2))
def charts():
 pp=[p for p in permutations(range(2,6)) if p[0]%2==0]
 for L in combinations_with_replacement(pp,4):
  X=np.column_stack(([0,0,1,1],[0,1,0,1],np.array(L).T))
  if np.all((X//2==1).sum(1)==2):yield (X,)
def normX(X):
 # a,b are the first two component positions, c is position 2 and the last three interchangeable
 C=X[:,2:]
 ans=[]
 for ax in (0,):
  for flip in range(4):
   perm=[((((i%2)*2+i//2) if ax else i)^flip) for i in range(4)]
   for flipwing in (0,2):
    V=(C[perm]-2)^flipwing
    V^=(V[0]&1)[None,:]
    ans.append((tuple(V[:,0]),*sorted(tuple(u) for u in V[:,1:].T)))
 return min(ans)
def xxchart():
 keys=set()
 for X,*_ in charts():
  for ci in range(2,6):
   Z=X[:,[0,1,ci]+[j for j in range(2,6) if j!=ci]]
   keys.add(normX(Z))
 return [np.column_stack(([0,0,1,1],[0,1,0,1],(np.array(k)+2).T)) for k in sorted(keys)]
def ys(aa,bb):
 pp=list(permutations(range(2,6))); arr=[];kt=[j for j in range(6) if j not in (aa,bb)];out=[]
 for L in product(pp,repeat=4):
  if any(sum(v//2==1 for v in col)!=2 for col in zip(*L)):continue
  Y=np.zeros((4,6),int);Y[:,aa]=[0,0,1,1];Y[:,bb]=[0,1,0,1];Y[:,kt]=np.array(L).T
  out.append([Xid[tuple(v)] for v in Y])
 return np.array(out,dtype=np.int32)
def pairinfo(A,B):
 # A,B are IDs arrays. Return zero/nonadj cross Gram mod7 and capacity.
 qa=T[A];qb=T[B];k=(qa[:,None,:]//2==qb[None,:,:]//2).sum(-1);eq=(qa[:,None,:]==qb[None,:,:]);n=eq.sum(-1)
 c=((qa[:,None,:]//2!=qb[None,:,:]//2)&(qa[:,None,:]%2==qb[None,:,:]%2)).sum(-1)
 ok=n<=2
 for w in range(3):ok &= ((eq & (qa[:,None,:]//2==w)).sum(-1)<=1)
 return ((43-18*n-4*k-6*c)%7).astype(np.int16),ok
xx=xxchart();print('first profiles',len(xx),flush=True);ys0=ys(0,2);print('all second',len(ys0),flush=True)

def batrank(a):
 a=np.array(a,dtype=np.int16)%7
 n,m,k=a.shape;rr=np.zeros(n,dtype=int);R0=np.arange(n)
 for col in range(k):
  ci=(np.arange(m)[None,:]>=rr[:,None])&(a[:,:,col]!=0)
  good=ci.any(1);w=R0[good]
  if not len(w):continue
  pr=rr[w];i=ci[w].argmax(1)
  b=a[w,pr].copy();a[w,pr]=a[w,i];a[w,i]=b
  b=(a[w,pr]*np.array([0,1,4,5,2,3,6],dtype=np.int16)[a[w,pr,col]][:,None])%7
  a[w]=(a[w]-a[w,:,col,None]*b[:,None,:])%7;a[w,pr]=b;rr[w]+=1
 return rr
def squaresets(yy):
 uq,inv=np.unique(yy,return_inverse=True);iv=inv.reshape(yy.shape)
 v,ok=pairinfo(uq,uq)
 vals=(v[iv[:,:,None],iv[:,None,:]]-4*np.array([[int((i^j) in (1,2)) for j in range(4)] for i in range(4)]))%7
 vals[:,np.arange(4),np.arange(4)]=0
 assert np.all(vals.sum(1)%7==0)
 return uq,iv,vals,batrank(vals[:,:3,:3])
yu,yi,YR,Yrank=squaresets(ys0)
xxid=np.array([[Xid[tuple(t)] for t in X] for X in xx])
xu,xi,XR,Xrank=squaresets(xxid)
def firstpair(ii):
 x=xxid[ii];a,ok=pairinfo(x,yu);v=a[:,yi].transpose(1,0,2)
 mask=(Yrank>=2)&(Xrank[ii]>=2)&(ok[:,yi].all((0,2)))&((v.sum(1)%7==0).all(1))&((v.sum(2)%7==0).all(1))
 sel=np.where(mask)[0];c=v[sel,:3,:3];G=np.zeros((len(sel),6,6),np.int16);G[:,:3,:3]=XR[ii,:3,:3];G[:,3:,3:]=YR[sel,:3,:3];G[:,:3,3:]=c;G[:,3:,:3]=c.transpose(0,2,1)
 rank=batrank(G);return sel,G,rank

inv7=np.array([0,1,4,5,2,3,6],dtype=np.int16)
def invs(ss):
 n,d,_=ss.shape;a=np.tile(np.eye(d,dtype=np.int16),(n,1,1));b=ss.copy();row=np.arange(n);det=np.ones(n,np.int16)
 for j in range(d):
  non=b[:,j:,j]!=0;k=non.argmax(1)+j;det*=np.where(k==j,1,-1).astype(np.int16)
  for M in [a,b]:
   x=M[:,j].copy();M[:,j]=M[row,k];M[row,k]=x
  piv=b[:,j,j].copy();det=det*piv%7; iv=inv7[piv];b[:,j]=b[:,j]*iv[:,None]%7;a[:,j]=a[:,j]*iv[:,None]%7
  f=b[:,:,j].copy();f[:,j]=0;b=(b-f[:,:,None]*b[:,None,j])%7;a=(a-f[:,:,None]*a[:,None,j])%7
 return a,det

def ijcap(X):
 bad=[]
 for i,j in pairs:
  for (a,b),n in Counter(map(tuple,X[:,[i,j]])).items():
   if n>2-(a//2==b//2):bad.append((int(i),int(j),int(a),int(b),int(n)))
 return bad

# Two fixed squares, remaining rows known to touch the shared 0 parent.
O=np.where((T[:,0]//2==0)&(T[:,1]//2!=0)&(T[:,2]//2!=0))[0]
# six (=3 choices of second axis and 2 parent signs) classes of 96 each under each common sign
cls=np.array([np.where((T[O,0]==s)&(T[O,d]==e))[0] for s in range(2) for d in (3,4,5) for e in (0,1)])
# lookup required pair quota / occupancy for all source-pair incidence slots
pairKey=np.array([6*T[:,i]+T[:,j]+36*q for q,(i,j) in enumerate(pairs)]).T.astype(np.int16)
pairCap=np.tile(np.array([2-(i//2==j//2) for i in range(6) for j in range(6)],int),15)
VP,OK=pairinfo(O,O);NN=(T[O,None,:]==T[O][None,:,:]).sum(2)
# An actual six-row cover for a fixed common-parent sign must also have all symbol counts.
def cover(ss,options,sgn,gram=None):
 base=ss[T[ss,0]==sgn];key=(6*np.arange(5)[None,:]+T[O,1:]).astype(np.int16)
 rhs=np.tile([1,1,2,2,2,2],5)-np.bincount((T[base,1:]+6*np.arange(5)[None,:]).ravel(),minlength=30)
 opt=[np.where(options&np.isin(np.arange(len(O)),cls[j]))[0] for j in range(6*sgn,6*sgn+6)];opt.sort(key=len)
 if not all(map(len,opt)):return None
 # On a rank-five base, every candidate residual is completely determined.
 sub=np.concatenate(opt);gid=np.full(len(O),-1,dtype=np.int16);gid[sub]=np.arange(len(sub))
 if gram is not None:
  W,P=gram
  adj=(2*(VP[np.ix_(sub,sub)]-W[:,sub].T@P[:,sub]))%7
  np.fill_diagonal(adj,0)
  good=(adj<=1)&(NN[np.ix_(sub,sub)]+adj<=2)
 def go(k,sel):
  if k==6:
   assert not rhs.any()
   if gram is not None and not (adj[np.ix_(gid[sel],gid[sel])].sum(1)==1).all():return None
   return tuple(sel)
  for b in opt[k]:
   if np.any(rhs[key[b]]==0):continue
   if sel and not OK[b,np.array(sel,int)].all():continue
   if gram is not None and sel and (not good[gid[b],gid[sel]].all() or adj[gid[b],gid[sel]].sum()>1):continue
   rhs[key[b]]-=1;r=go(k+1,sel+[b]);rhs[key[b]]+=1
   if r is not None:return r
  return None
 return go(0,[])
def nv(v):
 j=next(i for i,x in enumerate(v) if x);return tuple((v*inv7[v[j]])%7)
def lower(ii):
 x=xxid[ii];sel,G,rk=firstpair(ii);assert np.all((rk>=3)&(rk<=6))
 v,ox=pairinfo(x,O);vy,oy=pairinfo(yu,O);ct=Counter();out=[];sq={0,1,2,4}
 for k in np.where(rk<=5)[0]:
  h=int(rk[k]);assert h in (3,4,5);s=sel[k];gg=G[k]
  for J in combinations(range(6),h):
   J=list(J);bi,d0=invs(gg[J,:][:,J][None])
   if d0[0]:break
  assert d0[0];w=np.vstack((v[:3],vy[yi[s,:3]]));pr=bi[0]@w[J]%7;dv=(w-gg[:,J]@pr)%7;norm=(-(pr*w[J]).sum(0))%7;old=np.r_[x,ys0[s]]
  prev=np.bincount(pairKey[old].ravel(),minlength=540)
  ok=(prev[pairKey[O]]<pairCap[pairKey[O]]).all(1)&ox.all(0)&oy[yi[s]].all(0)
  if h==5:
   masks=[("sole",ok&(dv==0).all(0)&(norm==0))]
  elif h==4:
   ok1=ok&(dv==0).all(0)
   masks=[(str(e),ok1&np.isin((norm*e)%7,[0,1,2,4])) for e in (1,3)]
  else:
   zero=(dv==0).all(0);forms={nv(u) for u in dv[:,ok&~zero].T}
   masks=[('0',ok&zero)] # no extra radical; norm condition harmlessly omitted in dimension two
   for a in forms:
    aa=np.array(a);j=next(i for i,z in enumerate(a) if z);col=dv[j]
    masks.append((str(a),ok&(dv==aa[:,None]*col[None,:]%7).all(0)&((col!=0)|(norm==0))))
  ct['base',h]+=1
  for name,mask in masks:
   if not mask[cls].any(1).all():continue
   ct['available',h]+=1;a=cover(old,mask,0,(w[J],pr) if h==5 else None)
   if a is None:continue
   ct['cover0',h]+=1;out.append((ii,int(s),h,name,a))
 return ct,out

if __name__=='__main__':
 from time import monotonic
 tic=monotonic();C=Counter();ret=[]
 assert len(xx)==108
 for ii in range(len(xx)):
  ct,r=lower(ii);C.update(ct);ret+=r
 print('two-square rank/row-availability counts:',dict(C),'feasible rooted six-fans:',len(ret),'seconds',round(monotonic()-tic,1))
 assert not ret and C=={('base',5):52144,('base',4):1945,('base',3):42,('available',5):156,('available',4):4}
 print('The induced clean-axis graph off a saturated axis is a matching at rank 36.')
