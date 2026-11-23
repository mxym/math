"""Rank-36 saturated axis cannot support two more disjoint clean pairs.
NumPy only. Run with OPENBLAS_NUM_THREADS=1. All Gram arithmetic is over F7.
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
 C=X[:,2:];out=[]
 for sw in (0,1):
  for flip in range(4):
   idx=[(i//2+2*(i%2) if sw else i)^flip for i in range(4)]
   for wg in (0,2):
    v=(C[idx]-2)^wg;v^=(v[0]&1)[None,:]
    out.append((*sorted(tuple(x) for x in v[:,:2].T),*sorted(tuple(x) for x in v[:,2:].T)))
 return min(out)
def xxchart():
 keys=set()
 for X,*_ in charts():
  for cc in combinations(range(2,6),2):
   keys.add(normX(X[:,[0,1,*cc,*[i for i in range(2,6) if i not in cc]]]))
 return [np.column_stack(([0,0,1,1],[0,1,0,1],(2+np.array(k)).T)) for k in sorted(keys)]
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
xx=xxchart();print('first profiles',len(xx),flush=True);ys0=ys(2,3);print('all second',len(ys0),flush=True)

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


P4=list(permutations(range(4)));ADB=np.array([[int((i^j) in (1,2)) for j in range(4)] for i in range(4)],np.int16)
def match2(ii):
 x=xxid[ii];sv=[];ct=Counter();vx,ok=pairinfo(x,yu);nx=(T[x,None,:]==T[yu][None,:,:]).sum(2)
 for pp in P4:
  E=np.eye(4,dtype=np.int16)[:,pp];cap=2-E-ADB@E-E@ADB
  V=(vx[:,yi].transpose(1,0,2)-4*E[None,:,:])%7
  good=(nx[:,yi].transpose(1,0,2)<=cap[None,:,:]).all((1,2))&(Xrank[ii]>=2)&(Yrank>=2)&(ok[:,yi].all((0,2)))&((V.sum(1)%7==0).all(1))&((V.sum(2)%7==0).all(1))
  idx=np.where(good)[0];G=np.zeros((len(idx),6,6),dtype=np.int16);C=V[idx,:3,:3]
  G[:,:3,:3]=XR[ii,:3,:3];G[:,3:,3:]=YR[idx,:3,:3];G[:,:3,3:]=C;G[:,3:,:3]=C.transpose(0,2,1);rk=batrank(G);ct.update(rk.tolist())
  sv.append((pp,idx[rk<=5],G[rk<=5],rk[rk<=5]))
 return ct,sv

cross=[(i,j) for i in (0,1) for j in (2,3)]
O=np.where((np.sum(T[:,:2]//2==0,axis=1)==1)&(np.sum(T[:,2:4]//2==0,axis=1)==1))[0]
cls=np.array([np.where((T[O,i]==s)&(T[O,j]==t))[0] for i,j in cross for s,t in product(range(2),repeat=2)])
vY0,oY0=pairinfo(yu,O)

pairkey=np.array([6*T[:,a]+T[:,b]+36*i for i,(a,b) in enumerate(pairs)]).T
cap=np.tile([2-(a//2==b//2) for a in range(6) for b in range(6)],15)
def AC(ok,old,w,pr):
 quota=cap-np.bincount(pairkey[old].ravel(),minlength=540)
 ok=ok&(quota[pairkey[O]]>0).all(1)
 a=np.where(ok)[0];rr=[np.where(np.isin(a,g))[0] for g in cls]
 if not all(map(len,rr)):return 0
 raw=O[a];B,Okk=pairinfo(raw,raw);n=(T[raw,None,:]==T[raw][None,:,:]).sum(2)
 adj=(2*(B-w[:,a].T@pr[:,a]))%7
 allowed=Okk&(adj<=1)&(adj+n<=2)
 for c in np.where(quota<=1)[0]:
  rr0=np.where((pairkey[raw]==c).any(1))[0];allowed[np.ix_(rr0,rr0)]=0
 for step in range(32):
  tt=[list(z) for z in rr]
  for i in range(16):
   if not len(rr[i]):return 1
   for j in range(16):
    if i!=j:rr[i]=rr[i][np.any(allowed[np.ix_(rr[i],rr[j])],axis=1)]
  if any(not len(z) for z in rr):return 1
  if all(len(z)==len(z0) for z,z0 in zip(rr,tt)):break
 return 2
def filterm(ii):
 x=xxid[ii];base,sblk=match2(ii);v,ox=pairinfo(x,O);out=Counter();kept=[]
 for perm,sl,G,rk in sblk:
  carry=rk==5
  for miss in range(6):
   if not carry.any():break
   I=[j for j in range(6) if j!=miss];rr=np.where(carry)[0];b,dt=invs(G[rr][:,I,:][:,:,I]);a=dt!=0
   ix=rr[a];b=b[a];carry[ix]=0
   for start in range(0,len(ix),32):
    ix1=ix[start:start+32];bi=b[start:start+32];ss=sl[ix1]
    w=np.concatenate((np.broadcast_to(v[:3][None,:],(len(ss),3,len(O))),vY0[yi[ss,:3]]),1)
    proj=bi@w[:,I]%7
    ok=ox.all(0)[None,:]&oY0[yi[ss]].all(1)&((G[ix1,miss,:][:,I,None]*proj).sum(1)%7==w[:,miss])&((proj*w[:,I]).sum(1)%7==0)
    # All sixteen signed-parent choices are independently mandatory.
    order=np.where(ok[:,cls].any(2).all(1))[0];out['pass5']+=len(order);out['all5']+=len(ss)
    for j in order:
     lev=AC(ok[j],np.r_[x,ys0[ss[j]]],w[j,I],proj[j]);out[lev]+=1
     if lev==2:kept.append((ii,ss[j],perm))
  assert not carry.any()
 return base,out,kept

def nv(x):
 j=np.where(x!=0)[0][0];return tuple(x*inv7[x[j]]%7)
def lowerX(ii):
 x=xxid[ii];b,sblk=match2(ii);vx,ox=pairinfo(x,O);tot=Counter();out=[]
 for pp,sel,G,rk in sblk:
  for h in (2,3,4):
   carry=rk==h
   for J in combinations(range(6),h):
    if not carry.any():break
    J=list(J);take=np.where(carry)[0];B,dt=invs(G[take][:,J,:][:,:,J]);good=dt!=0
    if not good.any():continue
    q0=take[good];B=B[good];carry[q0]=0
    for st in range(0,len(q0),32):
     ix=q0[st:st+32];idx=sel[ix];bi=B[st:st+32]
     w=np.concatenate((np.broadcast_to(vx[:3][None,:],(len(ix),3,len(O))),vY0[yi[idx,:3]]),1);pr=bi@w[:,J]%7
     dv=(w-G[ix][:,:,J]@pr)%7;nu=(-(w[:,J]*pr).sum(1))%7;ok=ox.all(0)[None,:]&oY0[yi[idx]].all(1);tot['all',h]+=len(ix)
     for ii0 in range(len(ix)):
      ss=idx[ii0];old=np.r_[x,ys0[ss]];qt=cap-np.bincount(pairkey[old].ravel(),minlength=540)
      ok0=ok[ii0]&(qt[pairkey[O]]>0).all(1);zero=(dv[ii0]==0).all(0);opts=[]
      if h==4:
       for sign in (1,3):
        opts.append((sign,ok0&zero&np.isin(nu[ii0]*sign%7,[0,1,2,4])))
      elif h==3:
       opts.append((0,ok0&zero));forms={nv(y) for y in dv[ii0,:,ok0&~zero]}
       for f in forms:
        q=np.array(f);i=next(i for i,z in enumerate(q) if z);t=dv[ii0,i];opts.append((f,ok0&(dv[ii0]==q[:,None]*t[None,:]%7).all(0)&((t!=0)|(nu[ii0]==0))))
      else:opts.append((None,ok0))
      for name,mask in opts:
       if mask[cls].any(1).all():
        tot['pass',h]+=1;out.append((ii,int(ss),pp,h,name))
   assert not carry.any()
 return tot,out

def lowAC(ii,ss,pp,h,name,ret=False):
 x=xxid[ii];y=ys0[ss];E=np.eye(4,dtype=np.int16)[:,pp];v,ok=pairinfo(x,y);C=(v[:3,:3]-4*E[:3,:3])%7
 G=np.block([[XR[ii,:3,:3],C],[C.T,YR[ss,:3,:3]]]);J=next(list(j) for j in combinations(range(6),h) if invs(G[None,:,:][:,j,:][:,:,j])[1][0])
 bi=invs(G[None,:,:][:,J,:][:,:,J])[0][0];vx,ox=pairinfo(x,O);w=np.concatenate((vx[:3],vY0[yi[ss,:3]]));pr=bi@w[J]%7;dv=(w-G[:,J]@pr)%7;nu=(-(w[J]*pr).sum(0))%7
 qt=cap-np.bincount(pairkey[np.r_[x,y]].ravel(),minlength=540)
 base=ox.all(0)&oY0[yi[ss]].all(0)&(qt[pairkey[O]]>0).all(1)
 # with fixed radical-alpha zero, residual ambient dimension 5-h; if h=2 each X spans3, alpha cannot actually be all 0.
 if h==4:spec=[(name,None)]
 elif h==3 and name==0:spec=[(1,None),(3,None)]
 elif h==3:spec=[(0,np.array(name))]
 else:
  fs={nv(v) for v in dv[:,base].T if v.any()};fs.add(None)
  spec=[(eps,np.array(f) if f is not None else None) for f in fs for eps in (1,3)]
 for eps,alpha in spec:
  if alpha is None:
   u=(dv==0).all(0)&base
   if h==2:
    # require only y=0, model full 3-space; if all differences invisible, all residuals in perpendicular of a common visible radical.
    F=np.array([(i,0,z) for i in range(7) for z in range(7)],np.int16);H=np.array([[0,1,0],[1,0,0],[0,0,eps]],np.int16)
   else:
    F=np.array(list(product(range(7),repeat=5-h)),np.int16);H=np.eye(5-h,dtype=np.int16);H[-1,-1]=eps
  else:
   j=next(j for j,s in enumerate(alpha) if s);t=dv[j];u=(dv==alpha[:,None]*t[None,:]%7).all(0)&base
   H=np.array([[0,1],[1,0]],np.int16) if h==3 else np.array([[0,1,0],[1,0,0],[0,0,eps]],np.int16)
   F=np.array(list(product(range(7),repeat=5-h)),np.int16)
  bi0=np.where(u)[0];mask=((F@H*F).sum(1)[:,None]%7==nu[bi0][None,:])
  if alpha is not None:mask &= (F[:,1,None]==t[bi0][None,:])
  ki,wi=np.where(mask);aa=bi0[wi];ff=F[ki];cc=[np.where(np.isin(aa,g))[0] for g in cls]
  if not all(map(len,cc)):continue
  size0=list(map(len,cc))
  def compatible(a,b):
   raw=O[aa[a]];ras=O[aa[b]]
   B,good=pairinfo(raw,ras);n=(T[raw,None,:]==T[ras][None,:,:]).sum(2);adj=(2*(B-w[J][:,aa[a]].T@pr[:,aa[b]]-ff[a]@H@ff[b].T))%7
   al=good&(adj<=1)&(adj+n<=2)
   for key in np.where(qt<=1)[0]:
    i=np.where((pairkey[raw]==key).any(1))[0];j=np.where((pairkey[ras]==key).any(1))[0]
    if len(i)*len(j):al[np.ix_(i,j)]=0
   return al
  # smallest domain first. Distinct classes, cap/existence cache implicit.
  for step in range(12):
   old=list(map(len,cc))
   for j in sorted(range(16),key=lambda j:len(cc[j])):
    if not len(cc[j]):break
    for i in range(16):
     if i!=j and len(cc[i]):cc[i]=cc[i][compatible(cc[i],cc[j]).any(1)]
   if not all(map(len,cc)):break
   if old==list(map(len,cc)):break
  if all(map(len,cc)):return (len(F),size0,list(map(len,cc)),eps,name) if ret else True
 return False

if __name__=='__main__':
 print('first/second diagrams',len(xx),len(ys0),'necessary signed classes, candidates',cls.shape)
 assert len(xx)==83 and len(ys0)==23040 and cls.shape==(16,96)
 C=Counter();D=Counter();L=Counter()
 for i in range(83):
  _,b,hi=filterm(i);C.update(b);assert not hi
  d,lo=lowerX(i);D.update(d)
  for q in lo:
   assert not lowAC(*q),q
   L[q[3]]+=1
 print('nonsingular individual pass/rank5:',C)
 print('lower counts:',D,'lifted and rejected:',L)
 assert C=={'all5':235198,'pass5':3059,1:2834,0:225}
 assert D=={('all',4):19644,('all',3):460,('all',2):2,('pass',3):158,('pass',4):110,('pass',2):2}
 assert L=={3:158,4:110,2:2}
 print('No disjoint clean pair off a saturated triangle at mod-seven rank 36.')
