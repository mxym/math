#!/usr/bin/env python3
"""All involutions of two nine-point strict charts: run all four or pass case 0--3."""
import itertools,sys,time,math
import numpy as np
from scipy.optimize import linprog
from threadpoolctl import threadpool_limits
threadpool_limits(1)
if not __debug__:raise RuntimeError('run without -O; exact guards must be enabled')
GRAPHS={10:[80,96,192,384,257,258,7,12,56],44:[48,224,448,384,257,3,6,14,28]}
def solve(G,tar,limit):
 n=len(G);K=4096;F0=600;E=list(itertools.combinations(range(n),2));ne=len(E)
 I=np.array([a for a,b in E]);J=np.array([b for a,b in E]);idx={e:k for k,e in enumerate(E)}
 strong=np.array([bool(G[a]>>b&1)for a,b in E]);deg=[g.bit_count()for g in G];start=time.time();goal=tar/1e6
 autos=[]
 for h in itertools.permutations(range(n)):
  if all(deg[a]==deg[h[a]]for a in range(n)) and all(bool(G[h[a]]>>h[b]&1)==st for (a,b),st in zip(E,strong)):
   autos.append([idx[tuple(sorted((h[a],h[b])))]for a,b in E])
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
 def verify(lo,hi,ls,bs,WI,PI,dual):
  D=10**14;den=4*K**4;H=den*F0**2;swi=len(WI);ss=len(sym);diag=0;tweight=0
  gco=[0]*ne;gc=0;wco=[0]*ne
  for ii in np.where(dual>1e-10)[0]:
   v0=float(dual[ii])
   if ii<swi:
    t=round(D*v0);w=list(map(int,Ws[WI[ii]]));tweight+=t;diag+=t*sum(c*c for c in w)
    for k,(a,b)in enumerate(E):wco[k]+=2*t*w[a]*w[b]
   elif ii<swi+ss:
    a,b=sym[ii-swi];t=round(D*v0);gco[a]+=t;gco[b]-=t
   else:
    v=list(map(int,Ps[PI[ii-swi-ss]]));norm=sum(c*c for c in v);t=round(D*v0/norm);gc+=t*norm
    for k,(a,b)in enumerate(E):gco[k]+=2*t*v[a]*v[b]
  upper=diag*(3*den//4)+gc*H
  for k in range(ne):
   c=wco[k]*int(ls[k])+gco[k]*(H//K)
   upper+=wco[k]*int(bs[k])+c*int(hi[k]if c>0 else lo[k])
  return (upper*10**6<=tar*tweight*H)if tweight else upper<0
 def go(lo,hi,ws0,ps0,depth):
  nonlocal noded,maxd
  noded+=1;maxd=max(maxd,depth)
  if noded>limit:return False
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
  lower=lo/K;upper=hi/K;bnds=[*zip(lower,upper),(0,1),(0,None)]
  ws=set(ws0)|set(range(Nbase));ps=set(ps0);prev=None
  for it in range(10):
   WI=sorted(ws);PI=sorted(ps);W=np.array([Ws[i]for i in WI])/F0;VV=np.array([Ps[i]for i in PI]);prod=2*W[:,I]*W[:,J]
   norm=(VV*VV).sum(axis=1);PA=-2.*VV[:,I]*VV[:,J]/norm[:,None]
   A=np.vstack([np.c_[-prod*sl,np.ones(len(W)),np.zeros(len(W))],np.c_[SY,np.zeros(len(sym)),-np.ones(len(sym))],np.c_[PA,np.zeros(len(VV)),-np.ones(len(VV))]])
   rhs=np.r_[.75*(W*W).sum(axis=1)+prod@ce,np.zeros(len(sym)),np.ones(len(VV))]
   r=linprog(np.r_[np.zeros(ne),-1.,12.],A_ub=A,b_ub=rhs,bounds=bnds,method='highs')
   if not r.success:print('LPFAIL',r.message);return False
   dual=np.maximum(0,-r.ineqlin.marginals)
   if -r.fun<=goal+.000002 and verify(lo,hi,ls,bs,WI,PI,dual):
    stats[1]+=1;certsum[0]+=len(np.where(dual>1e-10)[0]);return True
   g=r.x[:ne];Gram=np.eye(n);Gram[I,J]=Gram[J,I]=g;lam,U=np.linalg.eigh(Gram)
   Fc=np.eye(n)*.75;Fc[I,J]=Fc[J,I]=ce+sl*g;y=cap(Fc);c0=y@Fc@y
   T=np.eye(n)*.75;T[I,J]=T[J,I]=g**4-g*g/4;x=cap(T,y);c1=x@T@x
   if it==9:break
   new=False
   for j in np.where(lam<-.00025)[0]:
    h=addP(U[:,j]);new|=h not in ps;ps.add(h)
   for ww in (x,y):
    if ww@Fc@ww<r.x[ne]-.000003:
     h=addW(ww);new|=h not in ws;ws.add(h)
   if not new or (it>=5 and c0<r.x[ne]+.00001 and min(lam)>-.002):break
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
  stats[2]+=1
  return go(lo,h,ww,pp,depth+1) and go(l,hi,ww,pp,depth+1)
 ok=go(np.where(strong,-K,-K//2),np.where(strong,-K//2,K//2),set(range(Nbase)),set(range(len(Ps))),0)
 print('END',ok,noded,len(Ws),len(Ps),maxd,stats,certsum,round(time.time()-start,2),flush=True)
 return ok


CASES=[[10,[1,0,2,3,5,4,6,7,8]],[10,[4,5,3,2,0,1,8,7,6]],[10,[5,4,3,2,1,0,8,7,6]],[44,[0,8,7,6,5,4,3,2,1]]]
for j in (10,44):
 G=GRAPHS[j];n=len(G)
 autos={tuple(h) for h in itertools.permutations(range(n)) if all(G[a].bit_count()==G[h[a]].bit_count() for a in range(n)) and all(bool(G[a]>>b&1)==bool(G[h[a]]>>h[b]&1) for a,b in itertools.combinations(range(n),2))}
 expected={tuple(h)for g,h in CASES if g==j}|{tuple(range(n))}
 if autos!=expected:raise RuntimeError('incomplete automorphism coverage')
choice=range(len(CASES)) if len(sys.argv)==1 else [int(sys.argv[1])]
for i in choice:
 j,SYM=CASES[i];print('SYMM',j,SYM,flush=True)
 if not solve(GRAPHS[j],159960,95000):raise RuntimeError('open')
