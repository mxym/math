"""No saturated axis has a triangle of clean edges among its other axes, at mod-7 rank 36.
Verify the entire 12-site envelope; NumPy only, no floating point and no exterior graph search.
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
 for ax in (0,1):
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

zz0=ys(1,2);zu,zi,ZR,Zrank=squaresets(zz0);vYZ,okYZ=pairinfo(yu,zu)
# cap shared-neighbor margins between words where neighbors are unknown are not used
ixZ=np.array([np.where((T[zu,1]*2+T[zu,2])==i)[0] for i in range(4)])
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
def run():
 totals=Counter();cases=[]
 for ii in range(len(xx)):
  sel,G,rank=firstpair(ii);totals.update(('base',int(r)) for r in rank)
  vx,ox=pairinfo(xxid[ii],zu)
  # A row z has prescribed cross pairings w and square zero. At base rank 5 it
  # must lie in the actual basis; at 4, w must annihilate the two formal kernel vectors.
  # At base rank 3 do NOT require an actual relation.
  for h in (3,4,5):
   carry=rank==h
   for I0 in combinations(range(6),h):
    if not carry.any():break
    rem=np.where(carry)[0];I=list(I0);bs=G[rem][:,I,:][:,:,I]
    Bs,dt=invs(bs);act=dt!=0
    if not act.any():continue
    inds=rem[act];carry[inds]=False;Bs=Bs[act]
    for start in range(0,len(inds),64):
     i=inds[start:start+64];B=Bs[start:start+64];g=G[i];s=sel[i]
     w=np.concatenate((np.tile(vx[None,:3],(len(i),1,1)),vYZ[yi[s,:3]]),axis=1)
     ok=ox.all(0)[None,:]&okYZ[yi[s]].all(1)
     if h>=4:
      proj=B@w[:,I]%7;ok&=(((g[:,:,I]@proj)%7)==w).all(1)
      if h==5:ok&=((proj*w[:,I]).sum(1)%7==0)
     for v in np.where(ok[:,ixZ].any(2).all(1))[0]:
      iz=np.where(ok[v,zi].all(1)&(Zrank>=2))[0]
      if not len(iz):continue
      cz=w[v,:,zi[iz,:3]].transpose(0,2,1)
      allG=np.zeros((len(iz),9,9),dtype=np.int16)
      allG[:,:6,:6]=g[v];allG[:,:6,6:]=cz;allG[:,6:,:6]=cz.transpose(0,2,1);allG[:,6:,6:]=ZR[iz,:3,:3]
      rz=batrank(allG)
      for p in np.where(rz<=5)[0]:
       z=iz[p];bad=ijcap(T[np.r_[xxid[ii],ys0[s[v]],zz0[z]]])
       assert bad and any(n>=3 for a,b,u,vv,n in bad)
       cases.append((ii,int(s[v]),int(z),h,int(rz[p]),bad[0]))
       totals['full',h,int(rz[p])]+=1
   assert not carry.any()
 print('counts',dict(sorted(totals.items())))
 for c in cases:print(c)
 assert totals=={('base',3):28,('base',4):1072,('base',5):26709,('base',6):144619,('full',4,5):6,('full',5,5):14}
 print('All 20 necessary rank-at-most-five twelve-site diagrams exceed a literal symbol-pair quota.')
if __name__=='__main__':run()
