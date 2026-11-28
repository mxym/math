#!/usr/bin/env python3
"""Proof-producing replay of the single bare heptad complement bound 42.929023. Pass a filename to save its independently verifiable JSON tree (optional)."""
import json,sys,itertools,numpy as np
from fractions import Fraction as F
from threadpoolctl import threadpool_limits
threadpool_limits(1)
KGRID=4096;PUNIT=10**9
Kraw=[[[-597788,-398531,93327,479339,479339,93327,-398531],[-398531,-597788,-398531,93327,479339,479339,93327],[93327,-398531,-597788,-398531,93327,479339,479339],[479339,93327,-398531,-597788,-398531,93327,479339],[479339,479339,93327,-398531,-597788,-398531,93327],[93327,479339,479339,93327,-398531,-597788,-398531],[-398531,93327,479339,479339,93327,-398531,-597788]],[[-800100,-468063,168006,336904,355192,163683,-557160],[-468063,-507093,-371888,-149119,269565,269565,-166388],[168006,-371888,-800100,-718491,51765,293575,305697],[336904,-149119,-718491,-755691,-247442,25256,301123],[355192,269565,51765,-247442,-800100,-758009,-85947],[163683,269565,293575,25256,-758009,-800100,-308344],[-557160,-166388,305697,301123,-85947,-308344,-587507]],[[-496759,-441960,-239461,-138379,-264837,-345199,-369783],[-441960,-674550,-622077,-285229,-113444,98375,69884],[-239461,-622077,-732152,-570970,-193140,302361,298657],[-138379,-285229,-570970,-642498,-413034,31583,56377],[-264837,-113444,-193140,-413034,-493285,-397199,-367279],[-345199,98375,302361,31583,-397199,-760311,-752964],[-369783,69884,298657,56377,-367279,-752964,-748091]],[[-662831,-444638,-140537,245263,197936,-326845,-647475],[-444638,-785807,-690083,-39161,321609,151862,-92971],[-140537,-690083,-800100,-431613,34222,248537,209280],[245263,-39161,-431613,-800100,-645446,-76303,298988],[197936,321609,34222,-645446,-800100,-414336,18693],[-326845,151862,248537,-76303,-414336,-682808,-628799],[-647475,-92971,209280,298988,18693,-628799,-800100]],[[-559473,-461085,-19651,258576,33771,-412863,-551007],[-461085,-459390,-163217,72699,-64426,-379445,-415898],[-19651,-163217,-502434,-589989,-381298,-58249,24931],[258576,72699,-589989,-800100,-576786,84111,265417],[33771,-64426,-381298,-576786,-472463,-145038,2575],[-412863,-379445,-58249,84111,-145038,-459148,-459414],[-551007,-415898,24931,265417,2575,-459414,-574322]],[[-725986,-463470,-144943,207696,293730,-195503,-697263],[-463470,-727324,-695099,-189464,314938,208935,-161751],[-144943,-695099,-800100,-492033,102513,254085,146150],[207696,-189464,-492033,-720115,-531092,-173435,240406],[293730,314938,102513,-531092,-800100,-563905,66031],[-195503,208935,254085,-173435,-563905,-753116,-500258],[-697263,-161751,146150,240406,66031,-500258,-797376]]];W0=F(47904147,10**6);w0=F(4975124,10**6)
def rational_rows():
 I,J=np.triu_indices(7,1);E=list(zip(I,J));X=[]
 # Rebuild the affine/quadratic polynomial from rational matrices. Multiplying
 # by 10^6 before forming products keeps all raw matrix traces integral.
 basis=[np.eye(7,dtype=np.int64)]
 for i,j in E:
  T=np.zeros((7,7),dtype=np.int64);T[i,j]=T[j,i]=1;basis.append(T)
 A=np.array(basis);D=10**6
 for dat in Kraw:
  K=np.array(dat,np.int64);KS=K@A
  tt=np.trace(KS,axis1=1,axis2=2)
  Q=[]
  for i in range(22):
   row=[]
   for j in range(22):
    z=int(np.trace(KS[i]@A[j])+np.trace(KS[j]@A[i]))
    v=int(np.trace(KS[i]@KS[j]));u=int(tt[i])*int(tt[j]);row.append(F(z,4*49*D)+F(5*(6*v-u),168*49*D**2))
   Q.append(row)
  co=[Q[0][0]-W0*int(tt[0])/(12*w0*7*D)]
  co += [2*Q[0][i+1]-W0*int(tt[i+1])/(12*w0*7*D)for i in range(21)]
  ij=list(itertools.combinations_with_replacement(range(21),2))
  co += [(1+(i!=j))*Q[i+1][j+1]for i,j in ij]
  # Permute coefficients only after rounding, including the original cyclic witness.
  raw=np.array([a.numerator*PUNIT//a.denominator for a in co],np.int64);raw[0]+=len(raw)
  for sg in (-1,1):
   for sh in range(7):
    h=(sg*np.arange(7)+sh)%7;m=[E.index(tuple(sorted((h[i],h[j]))))for i,j in E]
    perm=[0]+[1+i for i in m]+[22+ij.index(tuple(sorted((m[i],m[j]))))for i,j in ij]
    X.append(raw[perm])
 XS=np.unique(X,axis=0)
 if not all(sum(abs(int(v))for v in row)*8*KGRID**2 <2**62 for row in XS):raise ValueError('machine integer bound')
 return XS
RK=rational_rows();nks=len(RK);DI,DJ=np.triu_indices(21);same=DI==DJ
def polytang(lo,hi,z):
 # One McCormick affine upper bound per mixed quadratic. All arrays are exact
 # signed integers on the KGRID coordinate grid.
 Qc=RK[:,22:];l=lo[DI][None,:];u=hi[DI][None,:];L=lo[DJ][None,:];U=hi[DJ][None,:]
 x=z[DI][None,:];y=z[DJ][None,:]
 a=np.where(Qc>=0,u,l);b=L;AA=np.where(Qc>=0,l,u);bb=U
 a1=a*y+b*x-a*b;aa1=AA*y+bb*x-AA*bb
 use=np.where(Qc>=0,a1<=aa1,a1>=aa1);a=np.where(use,a,AA);b=np.where(use,b,bb)
 a[:,same]=np.where(Qc[:,same]>=0,u[:,same],x[:,same]);b[:,same]=np.where(Qc[:,same]>=0,l[:,same],x[:,same])
 cc=(KGRID*KGRID)*RK[:,0]-np.sum(Qc*a*b,axis=1);aa=KGRID*RK[:,1:22].copy()
 for e in range(21):
  jj=np.where(DJ==e)[0];ii=np.where(DI==e)[0];aa[:,e]+=(Qc[:,jj]*a[:,jj]).sum(axis=1)+(Qc[:,ii]*b[:,ii]).sum(axis=1)
 return cc,aa

import itertools,sys,time,math
import numpy as np
from scipy.optimize import linprog
from threadpoolctl import threadpool_limits
threadpool_limits(1)
if not __debug__:raise RuntimeError('run without -O; exact guards must be enabled')
GRAPHS=[[],[[64,48,40,20,10,6,1],[66,49,40,20,10,6,1],[70,49,41,20,10,6,1],[112,76,34,18,9,5,3],[96,80,40,20,10,5,3],[96,84,42,20,10,5,3],[104,84,42,21,10,5,3],[112,112,40,20,11,7,3],[112,76,50,50,13,13,3]],[]]
def solve(G,tar,limit):
 n=len(G);K=4096;F0=600;E=list(itertools.combinations(range(n),2));ne=len(E)
 I=np.array([a for a,b in E]);J=np.array([b for a,b in E]);idx={e:k for k,e in enumerate(E)}
 strong=np.array([bool(G[a]>>b&1)for a,b in E]);deg=[g.bit_count()for g in G];start=time.time();goal=tar/1e6
 autos=[]
 for h in itertools.permutations(range(n)):
  if all(deg[a]==deg[h[a]]for a in range(n)) and all(bool(G[h[a]]>>h[b]&1)==st for (a,b),st in zip(E,strong)):
   autos.append([idx[tuple(sorted((h[a],h[b])))]for a,b in E])
 sym=[]
 for e in [*np.where(strong)[0],*np.where(~strong)[0]]:
  sym.extend((e,k)for k in set(h[e]for h in autos)-{e})
  autos=[h for h in autos if h[e]==e]
 SY=np.zeros((len(sym),ne))
 for i,(e,k)in enumerate(sym):SY[i,k]=1;SY[i,e]=-1
 def angles(lo,hi):
  Q=np.full((2*n,2*n),-K,dtype=np.int64);np.fill_diagonal(Q,K)
  Q[I,J]=Q[J,I]=Q[n+I,n+J]=Q[n+J,n+I]=lo
  Q[I,n+J]=Q[n+J,I]=Q[J,n+I]=Q[n+I,J]=-hi
  for i in range(2*n):
   a=Q[i][:,None];b=Q[i][None,:];z=(K*K-a*a)*(K*K-b*b)
   r=np.sqrt(z).astype(np.int64);r+=(r*r<z)
   assert np.all((r*r>=z)&((z==0)|((r-1)**2<z)))
   Q=np.maximum(Q,np.where(a+b>=0,(a*b-r)//K,-K))
  lo=Q[I,J].astype(int);hi=-Q[I,n+J].astype(int)
  if any(lo>hi)or np.any(Q[np.arange(n),n+np.arange(n)]> -K):return None,None
  return lo,hi
 def poly(lo,hi):
  l=lo.astype(np.int64);u=hi.astype(np.int64);den=4*K**4
  fl=4*l**4-l*l*K*K;fu=4*u**4-u*u*K*K
  co=(u<=0)&(24*u*u>=K*K)|(l>=0)&(24*l*l>=K*K)
  slope=np.where(co,(l+u)*(4*(l*l+u*u)-K*K),0)
  inter=np.where(co,fl-l*slope,np.maximum(np.maximum(fl,fu),np.where(l*u<=0,0,-den)))
  # Competing affine quartic majorants. A Bernstein upper bound over every
  # closed subinterval certifies the intercept for each integer slope.
  mid=l+u
  for SS in [(l+u)*(4*(l*l+u*u)-K*K)]+[16*t**3-2*K*K*t for t in ((3*l+u)//4,(l+u)//2,(l+3*u)//4)]:
   bound=np.full(len(l),-10**18,dtype=np.int64)
   for h in range(4):
    a=l+(u-l)*h//4;b=l+(u-l)*(h+1)//4;d=b-a
    fa=4*a**4-K*K*a*a-SS*a;fb=4*b**4-K*K*b*b-SS*b
    da=16*a**3-2*K*K*a-SS;db=16*b**3-2*K*K*b-SS
    v=np.maximum.reduce([12*fa,12*fa+3*d*da,12*fa+6*d*da+d*d*(48*a*a-2*K*K),12*fb-3*d*db,12*fb])
    bound=np.maximum(bound,v)
   ci=-((-bound)//12)
   use=(SS*mid+2*ci<slope*mid+2*inter)&(~co)
   slope=np.where(use,SS,slope);inter=np.where(use,ci,inter)
  return slope,inter
 def cap(F,w=None):
  x=np.ones(n)/n if w is None else w.copy();a=F@x
  for _ in range(120):
   i=np.argmax(np.where(x>1e-11,a,-1e6));k=np.argmin(a)
   if a[i]-a[k]<3e-7:break
   delta=min(x[i],(a[i]-a[k])/max(1e-12,F[i,i]+F[k,k]-2*F[i,k]))
   x[i]-=delta;x[k]+=delta;a+=delta*(F[:,k]-F[:,i])
  return x
 Ws=[];Ps=[];WM={};PM={};certsum=[0,0];stats=[0,0,0,0];noded=0;maxd=0
 def store(v,L,M):
  k=tuple(map(int,v))
  if k not in M:M[k]=len(L);L.append(np.array(k,dtype=int))
  return M[k]
 def addW(w):
  v=np.rint(F0*w).astype(int);v[np.argmax(v)]+=F0-v.sum();assert min(v)>=0
  return store(v,Ws,WM)
 def addP(v):
  x=np.rint(320*v/max(abs(v))).astype(int);x*=1 if x[np.argmax(abs(x))]>0 else -1
  return store(x,Ps,PM)
 addW(np.ones(n)/n)
 for j in range(1,1<<n):
  st=[i for i in range(n)if j>>i&1]
  if len(st)>=3 and all(not(G[a]>>b&1)for a,b in itertools.combinations(st,2)):addW(np.array([int(i in st)/len(st)for i in range(n)]))
 Nbase=len(Ws)
 for k in (3,4):
  for st in itertools.combinations(range(n),k):
   v=np.zeros(n);v[list(st)]=1;addP(v)
 certtree=[];UWM={};UPM={};SUMW=[];SUMP=[]
 def small(v,m,a):
  v=tuple(map(int,v));
  if v not in m:m[v]=len(a);a.append(v)
  return m[v]
 def verify(lo,hi,ls,bs,WI,PI,dual,extra):
  D=10**14;den=4*K**4;H=den*F0**2;swi=len(WI);ss=len(sym);diag=0;tweight=0
  gco=[0]*ne;gc=0;wco=[0]*ne;kt=0;kc=0;ka=[0]*ne;M0=49*PUNIT*K*K
  RR=[]
  for ii in np.where(dual>1e-10)[0]:
   v0=float(dual[ii])
   if ii<swi:
    t=round(D*v0);w=list(map(int,Ws[WI[ii]]));tweight+=t;diag+=t*sum(c*c for c in w)
    if t:RR.append([0,small(w,UWM,SUMW),t])
    for k,(a,b)in enumerate(E):wco[k]+=2*t*w[a]*w[b]
   elif ii<swi+ss:
    a,b=sym[ii-swi];t=round(D*v0);gco[a]+=t;gco[b]-=t
    if t:RR.append([1,int(ii-swi),t])
   elif ii<swi+ss+len(PI):
    v=list(map(int,Ps[PI[ii-swi-ss]]));norm=sum(c*c for c in v);t=round(D*v0/norm);gc+=t*norm
    if t:RR.append([2,small(v,UPM,SUMP),t])
    for k,(a,b)in enumerate(E):gco[k]+=2*t*v[a]*v[b]
   else:
    tt=round(D*v0);c0,cc,kid,anc=extra[ii-swi-ss-len(PI)];kt+=tt;kc+=tt*int(c0)
    if tt:RR.append([3,int(kid),tt,list(map(int,anc))])
    for k in range(ne):ka[k]+=tt*int(cc[k])
  tweight+=kt;upper=(diag*(3*den//4)+gc*H)*M0+kt*(3*H*M0//28)+49*H*kc
  for k in range(ne):
   wc=M0*wco[k]+2*(M0//49)*F0**2*kt
   c=wc*int(ls[k])+M0*gco[k]*(H//K)+49*H*ka[k]
   upper+=wc*int(bs[k])+c*int(hi[k]if c>0 else lo[k])
  ok=(upper*10**6<=tar*tweight*H*M0)if tweight else upper<0
  if ok:certtree.append(["D",RR])
  return ok
 def go(lo,hi,ws0,ps0,depth):
  nonlocal noded,maxd
  noded+=1;maxd=max(maxd,depth)
  if noded>limit:return False
  if noded%100==0:print('STAT',noded,depth,len(Ws),len(Ps),stats,round(time.time()-start,1),flush=True)
  lo,hi=angles(lo,hi)
  if lo is None:stats[0]+=1;certtree.append(['X']);return True
  # Enforce orbit ordering between all pair coordinates.
  for _ in range(2):
   change=False
   for a,b in sym:
    if lo[b]>lo[a]:lo[a]=lo[b];change=True
    if hi[a]<hi[b]:hi[b]=hi[a];change=True
   if not change:break
  if np.any(lo>hi):stats[0]+=1;certtree.append(['X']);return True
  den=4*K**4;ls,bs=poly(lo,hi);sl=ls.astype(float)*(K/den);ce=bs.astype(float)/den
  lower=lo/K;upper=hi/K;bnds=[*zip(lower,upper),(0,1),(0,None)]
  ws=set(ws0)|set(range(Nbase));ps=set(ps0);prev=None
  extra=[];ekeys=set()
  def addk(z):
   z=np.rint(np.clip(z,lower,upper)*K).astype(np.int64);cc,aa=polytang(lo,hi,z)
   vv=cc+(aa*z).sum(axis=1);added=0
   for i in np.argsort(vv)[:8]:
    key=(int(cc[i]),aa[i].tobytes())
    if key not in ekeys:extra.append((int(cc[i]),aa[i].copy(),i,z.copy()));ekeys.add(key);added+=1
   return added
  if nks:addk((lower+upper)/2)
  for it in range(12):
   WI=sorted(ws);PI=sorted(ps);W=np.array([Ws[i]for i in WI])/F0;VV=np.array([Ps[i]for i in PI]);prod=2*W[:,I]*W[:,J]
   norm=(VV*VV).sum(axis=1);PA=-2.*VV[:,I]*VV[:,J]/norm[:,None]
   A=np.vstack([np.c_[-prod*sl,np.ones(len(W)),np.zeros(len(W))],np.c_[SY,np.zeros(len(sym)),-np.ones(len(sym))],np.c_[PA,np.zeros(len(VV)),-np.ones(len(VV))]])
   rhs=np.r_[.75*(W*W).sum(axis=1)+prod@ce,np.zeros(len(sym)),np.ones(len(VV))]
   if extra:
    coeff=np.stack([v for u,v,ik,an in extra])/(PUNIT*K)+2*sl[None,:]/49
    intercept=np.array([u for u,v,ik,an in extra])/(PUNIT*K*K)+3/28+2*ce.sum()/49
    A=np.vstack((A,np.c_[-coeff,np.ones(len(extra)),np.zeros(len(extra))]));rhs=np.r_[rhs,intercept]
   r=linprog(np.r_[np.zeros(ne),-1.,12.],A_ub=A,b_ub=rhs,bounds=bnds,method='highs',options={'threads':1})
   if not r.success:print('LPFAIL',r.message);return False
   dual=np.maximum(0,-r.ineqlin.marginals)
   if -r.fun<=goal+.000002 and verify(lo,hi,ls,bs,WI,PI,dual,extra):
    stats[1]+=1;certsum[0]+=len(np.where(dual>1e-10)[0]);return True
   g=r.x[:ne];Gram=np.eye(n);Gram[I,J]=Gram[J,I]=g;lam,U=np.linalg.eigh(Gram)
   Fc=np.eye(n)*.75;Fc[I,J]=Fc[J,I]=ce+sl*g;y=cap(Fc);c0=y@Fc@y
   T=np.eye(n)*.75;T[I,J]=T[J,I]=g**4-g*g/4;x=cap(T,y);c1=x@T@x
   if it==11:break
   new=False
   if it in (0,2,5) and nks:new=bool(addk(g))
   for j in np.where(lam<-.00025)[0]:
    h=addP(U[:,j]);new|=h not in ps;ps.add(h)
   for ww in (x,y):
    if ww@Fc@ww<r.x[ne]-.000003:
     h=addW(ww);new|=h not in ws;ws.add(h)
   if not new or (it>=6 and c0<r.x[ne]+.00001 and min(lam)>-.002):break
  wdeep={WI[j]for j in range(len(WI))if dual[j]>1e-9}|{addW(y),addW(x)}
  pdeep={PI[j]for j in range(len(PI))if dual[len(WI)+len(sym)+j]>1e-9}
  # Retain moderately recent parent directions; no accumulated dense LP across the tree.
  ww=(wdeep|set(sorted(ws,reverse=True)[:25])|set(sorted(ws0,reverse=True)[:12]))
  pp=(pdeep|set(sorted(ps,reverse=True)[:45])|set(sorted(ps0,reverse=True)[:20])|set(range(min(18,len(Ps)))))
  gap=(ce+sl*g-(g**4-g*g/4))*(y[I]*y[J]+x[I]*x[J]+.003)
  gap+=.00015*(upper-lower)*(1+strong);gap[hi<=lo+1]=-1
  e=int(np.argmax(gap))
  if gap[e]<0 or depth>110:print('OPEN',noded,depth,-r.fun,c1,lam[0],flush=True);return False
  t=round(min(.80*upper[e]+.20*lower[e],max(.20*upper[e]+.80*lower[e],g[e]))*K)
  t=min(hi[e]-1,max(lo[e]+1,t));l=lo.copy();h=hi.copy();l[e]=h[e]=t
  stats[2]+=1;certtree.append([int(e),int(t)])
  return go(lo,h,ww,pp,depth+1) and go(l,hi,ww,pp,depth+1)
 ok=go(np.where(strong,-K,-K//2),np.where(strong,-K//2,K//2),set(range(Nbase)),set(range(len(Ps))),0)
 print('END',ok,noded,len(Ws),len(Ps),maxd,stats,certsum,round(time.time()-start,2),flush=True)
 if ok:
  import zlib,base64,hashlib
  dd={'W0':str(W0),'target':tar,'sym':[[int(x),int(y)]for x,y in sym],'masses':SUMW,'psd':SUMP,'tree':certtree,'kernels':Kraw}
  if len(sys.argv)==2:
   import pathlib
   pathlib.Path(sys.argv[1]).write_text(json.dumps({'tree':base64.b64encode(zlib.compress(json.dumps(dd,separators=(',',':')).encode(),9)).decode()},separators=(',',':'))+'\n')
 return ok

g7=[(1<<((i+1)%7))|(1<<((i-1)%7))for i in range(7)]
tv=min(1/(w0+48-W0),1/w0+(W0**2/48-W0)/w0**2);target=(tv.numerator*10**6//tv.denominator)-1
print('RUN mixed',nks,'W',W0,'target',target,flush=True)
if target!=197134 or nks!=71:raise RuntimeError('wrong target or orbit count')
if len(sys.argv)==2 and sys.argv[1]=='--ingredients':
 print('PASS exact rational 71 polynomial setup');sys.exit(0)
if len(sys.argv)>2:raise SystemExit('usage: python3 verify_kissing_six_single_heptad_42929023.py [single-tree.json]')
if not solve(g7,target,150000):raise RuntimeError('tree not closed')
