#!/usr/bin/env python3
"""Reflected seven-cycle in a 75-point obstruction: exact integer leaf certification."""
import json,sys,itertools,numpy as np
from fractions import Fraction as F
from threadpoolctl import threadpool_limits
threadpool_limits(1)
KGRID=4096;PUNIT=10**9
Kraw=[[[-597788,-398531,93327,479339,479339,93327,-398531],[-398531,-597788,-398531,93327,479339,479339,93327],[93327,-398531,-597788,-398531,93327,479339,479339],[479339,93327,-398531,-597788,-398531,93327,479339],[479339,479339,93327,-398531,-597788,-398531,93327],[93327,479339,479339,93327,-398531,-597788,-398531],[-398531,93327,479339,479339,93327,-398531,-597788]],[[-800100,-468063,168006,336904,355192,163683,-557160],[-468063,-507093,-371888,-149119,269565,269565,-166388],[168006,-371888,-800100,-718491,51765,293575,305697],[336904,-149119,-718491,-755691,-247442,25256,301123],[355192,269565,51765,-247442,-800100,-758009,-85947],[163683,269565,293575,25256,-758009,-800100,-308344],[-557160,-166388,305697,301123,-85947,-308344,-587507]],[[-496759,-441960,-239461,-138379,-264837,-345199,-369783],[-441960,-674550,-622077,-285229,-113444,98375,69884],[-239461,-622077,-732152,-570970,-193140,302361,298657],[-138379,-285229,-570970,-642498,-413034,31583,56377],[-264837,-113444,-193140,-413034,-493285,-397199,-367279],[-345199,98375,302361,31583,-397199,-760311,-752964],[-369783,69884,298657,56377,-367279,-752964,-748091]],[[-662831,-444638,-140537,245263,197936,-326845,-647475],[-444638,-785807,-690083,-39161,321609,151862,-92971],[-140537,-690083,-800100,-431613,34222,248537,209280],[245263,-39161,-431613,-800100,-645446,-76303,298988],[197936,321609,34222,-645446,-800100,-414336,18693],[-326845,151862,248537,-76303,-414336,-682808,-628799],[-647475,-92971,209280,298988,18693,-628799,-800100]],[[-559473,-461085,-19651,258576,33771,-412863,-551007],[-461085,-459390,-163217,72699,-64426,-379445,-415898],[-19651,-163217,-502434,-589989,-381298,-58249,24931],[258576,72699,-589989,-800100,-576786,84111,265417],[33771,-64426,-381298,-576786,-472463,-145038,2575],[-412863,-379445,-58249,84111,-145038,-459148,-459414],[-551007,-415898,24931,265417,2575,-459414,-574322]],[[-725986,-463470,-144943,207696,293730,-195503,-697263],[-463470,-727324,-695099,-189464,314938,208935,-161751],[-144943,-695099,-800100,-492033,102513,254085,146150],[207696,-189464,-492033,-720115,-531092,-173435,240406],[293730,314938,102513,-531092,-800100,-563905,66031],[-195503,208935,254085,-173435,-563905,-753116,-500258],[-697263,-161751,146150,240406,66031,-500258,-797376]]];W0=F(47875666,10**6);w0=F(4975124,10**6)
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
def solve(G,tar,limit):
 n=len(G);K=4096;F0=600;E=list(itertools.combinations(range(n),2));ne=len(E)
 I=np.array([a for a,b in E]);J=np.array([b for a,b in E]);idx={e:k for k,e in enumerate(E)}
 strong=np.array([bool(G[a]>>b&1)for a,b in E]);deg=[g.bit_count()for g in G];start=time.time();goal=tar/1e6
 # Necessary scalar budget on every induced matching plus isolated vertices,
 # and every pair with an independent complement. Root and dynamic exact pruning.
 from math import isqrt
 from fractions import Fraction as Fr
 th=Fr(196099 if n==7 else 159966,10**6);budget=(10**6*th.denominator)//th.numerator
 def ff(t):return t**4-t*t/4
 sk={(a,b):j for j,(a,b) in enumerate(E)};Es=[j for j in range(ne)if strong[j]]
 mask=[g for g in G];rset=[];diss=[]
 for h in range(1,1<<n):
  nodes=[j for j in range(n)if h>>j&1];ed=[e for e in Es if h>>I[e]&1 and h>>J[e]&1]
  if any((G[i]&h).bit_count()>1 for i in nodes):continue
  if any(all((G[i]&(h|1<<u)).bit_count()<=1 for i in nodes+[u])for u in range(n)if not h>>u&1):continue
  if not ed:continue
  diss.append((ed,(len(nodes)-2*len(ed))*1333333))
 sr=np.array([[(1 if e in ee else 0)for e in Es]for ee,_ in diss],dtype=np.int64);is0=np.array([w for _,w in diss],dtype=np.int64)
 gr=[Fr(t,K) for t in range(K//2,K+1)]
 qtab=np.array([2666666]*(K//2)+[int(2*10**6/(Fr(3,4)+ff(t)))for t in gr],dtype=np.int64)
 def prunematch(lo,hi):
  if not len(diss):return True
  qq=qtab[-lo[Es]];tot=sr@qq+is0
  if np.any(tot>budget):return False
  cap=np.min(np.where(sr,budget-tot[:,None]+qq[None,:],4*10**6),axis=0)
  lev=np.searchsorted(-qtab,-cap,side='left');hi[Es]=np.minimum(hi[Es],1-lev)
  return bool(np.all(lo<=hi))
 rootlo=np.where(strong,-K,-K//2);roothi=np.where(strong,-K//2,K//2)
 for e in Es:
  a,b=E[e];RR={}
  for h in range(1,1<<n):
   if h>>a&1 or h>>b&1:continue
   ss=[i for i in range(n)if h>>i&1]
   if any(G[i]&h for i in ss):continue
   k=((G[a]|G[b])&h).bit_count();s=len(ss)
   if s not in RR or RR[s]>k:RR[s]=k
  def close(t):
   # V(r)=(r+sqrt(3(1-r^2)))/2 bounds any adjacent strength.
   den=K*10**7;r=Fr(t,K);z=3*(K*K-t*t)*10**14;h=isqrt(z);v=(r+Fr(h+(h*h<z),den))/2
   for s,k in RR.items():
    d=Fr(3,4*s);cc=Fr(k,2*s)*ff(v)
    if d>th and cc<th and (th-cc)**2>(Fr(3,4)-th)*(d-th):return True
   return False
  if close(K):
   ll=K//2;rr=K
   while ll+1<rr:
    mid=(ll+rr)//2
    if close(mid):rr=mid
    else:ll=mid
   assert close(rr);rootlo[e]=max(rootlo[e],-rr)
 assert prunematch(rootlo,roothi)
 print('MATCH-CELLS',[(int(rootlo[e]),int(roothi[e]))for e in Es],len(diss),flush=True)
 autos=[]
 for h in itertools.permutations(range(n)):
  if all(deg[a]==deg[h[a]]for a in range(n)) and all(bool(G[h[a]]>>h[b]&1)==st for (a,b),st in zip(E,strong)):
   autos.append([idx[tuple(sorted((h[a],h[b])))]for a,b in E])
 # Sharp joint strong-edge quartic envelope from their common neighbour.
 es=list(map(int,np.where(strong)[0]));ns=len(es);sid={v:i for i,v in enumerate(es)};PP=[]
 TT=[(-1500000,1500000)]
 for zz in ('1.5','1.55','1.60','1.62','1.64','1.68','1.72','1.73'):
  z=F(zz);slo=-4*z**3/9+7*z/6;inter=-z**4/9+7*z*z/12-slo*z
  b=slo.numerator*10**6//slo.denominator;aa=-((-inter.numerator*10**6)//inter.denominator)+2
  TT.append((aa,b))
 GO=[[1,289940,-184430,209100],[1,473841,-317170,301310],[1,101010,-41630,92430],[1,169910,-95990,143020],[1,528580,-352740,346620],[1,69760,-11960,53200],[1,575210,-388820,346810],[1,319780,-205530,228000],[1,506351,-339330,324690],[1,214580,-129410,169250],[1,131350,-66380,117460],[1,83290,-25650,72600],[1,506341,-340230,316200],[2,-67260,72470,82540],[2,283220,-92650,288150],[2,-178630,127150,22850],[2,973520,-388850,385410],[2,455361,-170140,399950],[2,112060,-13170,184260],[2,412240,-132650,161450],[2,22510,29290,132530],[2,215220,-61340,246080],[2,368250,-131270,342340],[2,270670,-66170,99050],[2,619650,-228410,248480],[2,139450,-2530,36290]];groups=[]
 for i,j in itertools.combinations(es,2):
  ep=set(E[i])^set(E[j])
  if len(ep)!=2:continue
  k=idx[tuple(sorted(ep))]
  st0=len(PP)
  PP.extend((i,j,k,1,aa,bb,0)for aa,bb in TT)
  for R,aa,bb,cc in GO:
   if R==1:PP.append((i,j,k,R,10*aa,10*bb,10*cc))
  groups.append(list(range(st0,len(PP))))
  for ii,jj in ((i,j),(j,i)):
   st0=len(PP);PP.extend((ii,jj,k,R,10*aa,10*bb,10*cc)for R,aa,bb,cc in GO if R==2);groups.append(list(range(st0,len(PP))))
 # This graph is a cycle: higher-valent stars never enter the proof.
 assert all(x==2 for x in deg)
 NL=len(PP);edgeY=np.zeros((NL,ns));edgeGX=np.zeros((NL,ne));pRHS=np.zeros(NL)
 for i0,(i,j,k,R,aa,bb,cc)in enumerate(PP):
  if i<0:
   for e in j:edgeY[i0,sid[e]]=1;edgeGX[i0,e]=bb/1e6
   pRHS[i0]=aa/1e6;continue
  edgeY[i0,sid[i]]=R;edgeY[i0,sid[j]]=1;edgeGX[i0,i]=R*bb/1e6;edgeGX[i0,j]=bb/1e6;edgeGX[i0,k]=-cc/1e6;pRHS[i0]=aa/1e6
 exactperm=[idx[tuple(sorted((SYM[i],SYM[j])))]for i,j in E]
 assert sorted(SYM)==list(range(n)) and all(SYM[SYM[i]]==i for i in range(n))
 assert all(strong[j]==strong[exactperm[j]]for j in range(ne))
 autos=[h for h in autos if all(h[exactperm[j]]==exactperm[h[j]]for j in range(ne))]
 sym=[]
 for e in [*np.where(strong)[0],*np.where(~strong)[0]]:
  sym.extend((e,k)for k in set(h[e]for h in autos)-{e})
  autos=[h for h in autos if h[e]==e]
 for e,k in enumerate(exactperm):
  if e!=k:sym.append((e,k))
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
 def verify(lo,hi,ls,bs,WI,PI,dual,extra,TI):
  D=10**14;den=4*K**4;H=den*F0**2;swi=len(WI);ss=len(sym);diag=0;tweight=0
  gco=[0]*ne;gc=0;wco=[0]*ne;kt=0;kc=0;ka=[0]*ne;pc=0;pa=[0]*ne;ts=[0]*ne;M0=49*PUNIT*K*K
  for ii in np.where(dual>1e-10)[0]:
   v0=float(dual[ii])
   if ii<swi:
    t=round(D*v0);w=list(map(int,Ws[WI[ii]]));tweight+=t;diag+=t*sum(c*c for c in w)
    for k,(a,b)in enumerate(E):wco[k]+=2*t*w[a]*w[b]
   elif ii<swi+ss:
    a,b=sym[ii-swi];t=round(D*v0);gco[a]+=t;gco[b]-=t
   elif ii<swi+ss+len(PI):
    v=list(map(int,Ps[PI[ii-swi-ss]]));norm=sum(c*c for c in v);t=round(D*v0/norm);gc+=t*norm
    for k,(a,b)in enumerate(E):gco[k]+=2*t*v[a]*v[b]
   elif ii<swi+ss+len(PI)+len(extra):
    tt=round(D*v0);c0,cc=extra[ii-swi-ss-len(PI)];kt+=tt;kc+=tt*int(c0)
    for k in range(ne):ka[k]+=tt*int(cc[k])
   elif ii>=swi+ss+len(PI)+len(extra)+ns:
    jj=TI[ii-swi-ss-len(PI)-len(extra)-ns];i,j,k,R,aa,bb,cc=PP[jj];t=round(D*v0);pc+=t*aa
    if i<0:
     for e in j:pa[e]-=t*bb;ts[e]+=t
    else:pa[i]-=t*R*bb;pa[j]-=t*bb;pa[k]+=t*cc;ts[i]+=t*R;ts[j]+=t
  scalarweight=tweight;tweight+=kt;upper=(diag*(3*den//4)+gc*H)*M0+kt*(3*H*M0//28)+49*H*kc
  upper=upper*10**6+pc*H*M0
  for k in range(ne):
   wc=M0*(wco[k]-ts[k]*F0**2)+2*(M0//49)*F0**2*kt
   if wc<0:
    if not strong[k]:raise ValueError('negative weak-edge coefficient')
    wc=0 # the true strong-edge quartic is nonnegative
   c=10**6*(wc*int(ls[k])+M0*gco[k]*(H//K)+49*H*ka[k])+pa[k]*M0*(H//K)
   upper+=10**6*wc*int(bs[k])+c*int(hi[k]if c>0 else lo[k])
  return (upper<=tar*tweight*H*M0+110*scalarweight*H*M0)if tweight else upper<0
 def go(lo,hi,ws0,ps0,depth):
  nonlocal noded,maxd
  noded+=1;maxd=max(maxd,depth)
  if noded>limit:return False
  if noded%100==0:print('STAT',noded,depth,len(Ws),len(Ps),stats,round(time.time()-start,1),flush=True)
  if not prunematch(lo,hi):stats[0]+=1;return True
  lo,hi=angles(lo,hi)
  if lo is None:stats[0]+=1;return True
  # Enforce orbit ordering between all pair coordinates.
  for _ in range(2):
   change=False
   for a,b in sym:
    if lo[b]>lo[a]:lo[a]=lo[b];change=True
    if hi[a]<hi[b]:hi[b]=hi[a];change=True
   if not change:break
  if np.any(lo>hi):stats[0]+=1;return True
  den=4*K**4;ls,bs=poly(lo,hi);sl=ls.astype(float)*(K/den);ce=bs.astype(float)/den
  lower=lo/K;upper=hi/K;bnds=[*zip(lower,upper),*([(0,.75)]*ns),(0,1),(0,None)]
  ws=set(ws0)|set(range(Nbase));ps=set(ps0);prev=None
  extra=[];ekeys=set()
  def addk(z):
   z=np.rint(np.clip(z,lower,upper)*K).astype(np.int64);cc,aa=polytang(lo,hi,z)
   vv=cc+(aa*z).sum(axis=1);added=0
   for i in np.argsort(vv)[:8]:
    key=(int(cc[i]),aa[i].tobytes())
    if key not in ekeys:extra.append((int(cc[i]),aa[i].copy()));ekeys.add(key);added+=1
   return added
  if nks:addk((lower+upper)/2)
  useP=set()
  def pmix(z,y):
   slack=pRHS-edgeGX@z-edgeY@y
   for inds in groups:
    ids=np.array(inds);useP.update(ids[np.argsort(slack[ids])[:3]])
  cz=(lo+hi)/(2*K);pmix(cz,(cz[es]**4-cz[es]**2/4))
  for it in range(12):
   WI=sorted(ws);PI=sorted(ps);W=np.array([Ws[i]for i in WI])/F0;VV=np.array([Ps[i]for i in PI]);prod=2*W[:,I]*W[:,J]
   norm=(VV*VV).sum(axis=1);PA=-2.*VV[:,I]*VV[:,J]/norm[:,None]
   A=np.vstack([np.c_[-prod*sl,np.ones(len(W)),np.zeros(len(W))],np.c_[SY,np.zeros(len(sym)),-np.ones(len(sym))],np.c_[PA,np.zeros(len(VV)),-np.ones(len(VV))]])
   rhs=np.r_[.75*(W*W).sum(axis=1)+prod@ce-.000110,np.zeros(len(sym)),np.ones(len(VV))]
   if extra:
    coeff=np.stack([v for u,v in extra])/(PUNIT*K)+2*sl[None,:]/49
    intercept=np.array([u for u,v in extra])/(PUNIT*K*K)+3/28+2*ce.sum()/49
    A=np.vstack((A,np.c_[-coeff,np.ones(len(extra)),np.zeros(len(extra))]));rhs=np.r_[rhs,intercept]
   # Lift exactly the positive strong quartic entries. Mass and mixed rows no
   # longer use their individual secants until the separate edge bounds.
   nr=len(A);AY=np.zeros((nr,ns));gr=A[:,:ne].copy();br=rhs.copy()
   for tt in range(len(WI)):
    gr[tt,es]+=prod[tt,es]*sl[es];br[tt]-=prod[tt,es]@ce[es];AY[tt,:]=-prod[tt,es]
   if extra:
    ee=np.arange(nr-len(extra),nr);gr[np.ix_(ee,es)]+=2*sl[es][None,:]/49;br[ee]-=2*ce[es].sum()/49;AY[ee,:]=-2/49
   A=np.c_[gr,AY,A[:,ne:]]
   EB=np.zeros((ns,ne));EB[np.arange(ns),es]=-sl[es]
   TI=sorted(useP);A=np.vstack([A,np.c_[EB,np.eye(ns),np.zeros((ns,2))],np.c_[edgeGX[TI],edgeY[TI],np.zeros((len(TI),2))]]);rhs=np.r_[br,ce[es],pRHS[TI]]
   r=linprog(np.r_[np.zeros(ne+ns),-1.,12.],A_ub=A,b_ub=rhs,bounds=bnds,method='highs',options={'threads':1})
   if not r.success:print('LPFAIL',r.message);return False
   dual=np.maximum(0,-r.ineqlin.marginals)
   if -r.fun<=goal+.000002 and verify(lo,hi,ls,bs,WI,PI,dual,extra,TI):
    stats[1]+=1;certsum[0]+=len(np.where(dual>1e-10)[0]);return True
   g=r.x[:ne];Gram=np.eye(n);Gram[I,J]=Gram[J,I]=g;lam,U=np.linalg.eigh(Gram)
   Fc=np.eye(n)*.75;fcrow=ce+sl*g;fcrow[es]=r.x[ne:ne+ns];Fc[I,J]=Fc[J,I]=fcrow;y=cap(Fc);c0=y@Fc@y
   T=np.eye(n)*.75;T[I,J]=T[J,I]=g**4-g*g/4;x=cap(T,y);c1=x@T@x
   if it==11:break
   oldP=len(useP)
   if it in (0,3):pmix(g,r.x[ne:ne+ns])
   new=len(useP)>oldP
   if it in (0,2,5) and nks:new|=bool(addk(g))
   for j in np.where(lam<-.00025)[0]:
    h=addP(U[:,j]);new|=h not in ps;ps.add(h)
   for ww in (x,y):
    if ww@Fc@ww<r.x[ne+ns]-.000003:
     h=addW(ww);new|=h not in ws;ws.add(h)
   if not new or (it>=6 and c0<r.x[ne+ns]+.00001 and min(lam)>-.002):break
  wdeep={WI[j]for j in range(len(WI))if dual[j]>1e-9}|{addW(y),addW(x)}
  pdeep={PI[j]for j in range(len(PI))if dual[len(WI)+len(sym)+j]>1e-9}
  # Retain moderately recent parent directions; no accumulated dense LP across the tree.
  ww=(wdeep|set(sorted(ws,reverse=True)[:25])|set(sorted(ws0,reverse=True)[:12]))
  pp=(pdeep|set(sorted(ps,reverse=True)[:45])|set(sorted(ps0,reverse=True)[:20])|set(range(min(18,len(Ps)))))
  gap=(fcrow-(g**4-g*g/4))*(y[I]*y[J]+x[I]*x[J]+.003)
  gap+=.00015*(upper-lower)*(1+strong);gap[hi<=lo+1]=-1
  e=int(np.argmax(gap))
  if gap[e]<0 or depth>110:print('OPEN',noded,depth,-r.fun,c1,lam[0],flush=True);return False
  t=round(min(.80*upper[e]+.20*lower[e],max(.20*upper[e]+.80*lower[e],g[e]))*K)
  t=min(hi[e]-1,max(lo[e]+1,t));l=lo.copy();h=hi.copy();l[e]=h[e]=t
  stats[2]+=1
  return go(lo,h,ww,pp,depth+1) and go(l,hi,ww,pp,depth+1)
 ok=go(rootlo,roothi,set(range(Nbase)),set(range(len(Ps))),0)
 print('END',ok,noded,len(Ws),len(Ps),maxd,stats,certsum,round(time.time()-start,2),flush=True)
 return ok

SYM=[(-i)%7 for i in range(7)]
g7=[(1<<((i+1)%7))|(1<<((i-1)%7))for i in range(7)]
assert W0==F(47875666,10**6) and 1/(w0+48-W0)>F(196099,10**6) and 1/w0+(W0**2/48-W0)/w0**2>F(195989,10**6)
assert nks==71
if not solve(g7,195989,120000):raise RuntimeError("open")
