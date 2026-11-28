#!/usr/bin/env python3
"""General-polynomial seven-point Gram cells for the 132-point matching proof."""
#!/usr/bin/env python3
"""Continuous Gram-box certificate for the seven-/nine-point spherical quartic.
Usage: python3 verify-kissing-nine-gram-cells.py census | 7 [class] | 9 [class]
Requires Python 3.10+, NumPy, SciPy and threadpoolctl. LP and eigensolver outputs
only propose integer cuts; all successful region closures are integer checks.
Do not run Python with -O, since the range checks are assertions.
"""
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
  vals=[line(int(a),int(b)) for a,b in zip(lo,hi)]
  return np.array([v[0] for v in vals],dtype=np.int64),np.array([v[1] for v in vals],dtype=np.int64)
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
  if noded%300==0:print('STAT',noded,depth,len(Ws),len(Ps),stats,round(time.time()-start,1),flush=True)
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
   T=np.eye(n)*.75;T[I,J]=T[J,I]=np.polynomial.polynomial.polyval(g,FLOAT);x=cap(T,y);c1=x@T@x
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
  gap=(ce+sl*g-(np.polynomial.polynomial.polyval(g,FLOAT)))*(y[I]*y[J]+x[I]*x[J]+.003)
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

def census(n,alpha):
    # Enumerate by adding one vertex with an independent neighborhood. All filters
    # before the target size are hereditary. Canonical refinement + individualization.
    from functools import lru_cache
    def canon(G):
        def recur(part):
            while True:
                refined=[]
                for block in part:
                    groups={}
                    for i in block:
                        sig=tuple(sum((G[i]>>j)&1 for j in cell)for cell in part)
                        groups.setdefault(sig,[]).append(i)
                    refined.extend(tuple(groups[s])for s in sorted(groups))
                r=tuple(refined)
                if r==part:break
                part=r
            cell=next((j for j,x in enumerate(part)if len(x)>1),None)
            if cell is None:
                v=[b[0]for b in part]
                return tuple((G[v[i]]>>v[j])&1 for i in range(len(v))for j in range(i))
            a=part[cell];keys=[];seen=[]
            for x in a:
                if any((G[x]&~(1<<y))==(G[y]&~(1<<x))for y in seen):continue
                seen.append(x);rest=tuple(i for i in a if i!=x)
                keys.append(recur(part[:cell]+((x,),rest)+part[cell+1:]))
            return min(keys)
        return recur((tuple(range(len(G))),))
    vs=[()]
    for k in range(n):
        out={}
        for G in vs:
            for nb in range(1<<k):
                if nb.bit_count()>alpha or any(nb>>i&1 and (g&nb or g.bit_count()>=alpha)for i,g in enumerate(G)):continue
                B=tuple(g+(((nb>>i)&1)<<k)for i,g in enumerate(G))+(nb,)
                # Only an independent set using the newest vertex is new.
                av=[i for i in range(k)if not nb>>i&1]
                if any(all(not(B[i]>>j&1)for i,j in itertools.combinations(s,2))for s in itertools.combinations(av,alpha)):continue
                c=canon(B)
                if c not in out:out[c]=B
        vs=list(out.values())
    def fc(G):
        @lru_cache(None)
        def rec(mask):
            if not mask:return True
            h=mask&-mask;v=h.bit_length()-1;ss=G[v]&mask
            while ss:
                j=ss&-ss
                if rec(mask^h^j):return True
                ss^=j
            return False
        return all(rec(((1<<n)-1)^(1<<i))for i in range(n))
    if n==9:
        assert len(vs)==290
        vs=[g for g in vs if fc(g)]
    db=GRAPHS[{7:1,9:2}[n]]
    assert len(db)==len(vs)==({7:9,9:170}[n])
    assert {canon(g)for g in vs}=={canon(g)for g in db}
    print('PASS census',n,len(vs),flush=True)


from fractions import Fraction as Q
from functools import lru_cache
def add(a,b):return [(a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)for i in range(max(len(a),len(b)))]
def scale(a,v):return [v*x for x in a]
def init(ww):
 global H,FLOAT,ZZ
 gg=[[Q(1)],[Q(0),Q(1)]]
 for k in range(1,len(ww)):gg.append(add([0]+scale(gg[-1],Q(2*k+5,k+5)),scale(gg[-2],Q(-k,k+5))))
 A=[Q(0)]
 for k,w in enumerate(ww,1):A=add(A,scale(gg[k],w))
 K=4096;den=4*K**4;assert sum(A)==Q(3,4)
 M=sum(abs(v)*j*(j-1) for j,v in enumerate(A))
 err=M/(8*K*K)
 # Exact Horner at each integer grid knot. Endpoint + curvature bounds
 # imply any line majorizing these rounded-up knot values majorizes the real function.
 H=[];FLOAT=np.array([float(v)for v in A]);ZZ=np.arange(-K,K//2+1,dtype=np.int64)
 for a in ZZ:
  t=Q(int(a),K);xx=Q(0)
  for v in A[::-1]:xx=v+t*xx
  H.append(math.ceil(den*(xx+err)))
 assert max(abs(x) for x in H)<2**58
 H=np.array(H,dtype=np.int64)
@lru_cache(150000)
def line(l,u):
 K=4096;L=l+K;U=u+K
 if l==u:return 0,int(H[L])
 a=H[L:U+1];z=ZZ[L:U+1]
 sl={0,(int(H[U])-int(H[L]))//(u-l)}
 for e in ((3*L+U)//4,(L+U)//2,(L+3*U)//4):
  if e<U:sl.add(int(H[e+1])-int(H[e]))
 best=None
 for s in sl:
  assert abs(s)*K<2**59
  b=int(np.max(a-s*z));key=(s*(l+u)+2*b,abs(s),s,b)
  if best is None or key<best:best=key
 return best[2],best[3]
def main():
 from pathlib import Path
 import runpy,hashlib
 root=Path(__file__).resolve().parent
 # The quartic uses the public predecessor solver verbatim. Only targets change.
 old=root/'verify-kissing-seven-heptagon-boxes.py'
 if hashlib.sha256(old.read_bytes()).hexdigest()!='50c47966131b0324b1d31e4ca8ae6d926b12dc157022ea46aac5e49f94c0fe28':raise RuntimeError('different predecessor Gram solver')
 prior=runpy.run_path(str(old))
 arg=sys.argv[1:]or['all']
 if arg[0]=='census':prior['census'](7,3);return
 if arg[0] not in ('all','five','seven','degree10'):raise ValueError('choose all/five/seven/degree10/census')
 if arg[0]in ('all','five'):
  # With alpha<=2 the only triangle-free graph on five vertices is a pentagon.
  # All other five-point codes have C_f <= 1/4 by an independent triple.
  g5=[(1<<((i+1)%5))|(1<<((i+4)%5))for i in range(5)]
  if not prior['solve'](g5,250950,250000):raise RuntimeError('unclosed five-point tree')
  print('PASS five-point quartic .25095',flush=True)
 if arg[0]in ('all','seven'):
  # Eight non-C7 classes <=.20084, checked by the pinned predecessor.
  if not prior['solve'](prior['GRAPHS'][1][4],201000,400000):raise RuntimeError('unclosed cycle')
  print('PASS seven-point quartic .2010',flush=True)
 if arg[0]in ('all','degree10'):
  weights=[Q(0)]*10
  for k,v in [(2,9),(4,17),(10,10)]:weights[k-1]=Q(v,48)
  init(weights);ids=[int(x)for x in arg[1:]]if len(arg)>1 else range(9)
  if GRAPHS[1]!=prior['GRAPHS'][1]:raise ValueError('different graph representatives')
  for j in ids:
   if not 0<=j<9 or not solve(GRAPHS[1][j],180000,60000):raise RuntimeError('unclosed degree-ten cell '+str(j))
   print('PASS degree-ten',j,flush=True)
if __name__=='__main__':main()
