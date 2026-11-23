# Actual three norm18 fields, endpoint bridge path or triangle.
# Verification uses integer codegrees, exact integer Gram witnesses and Bareiss minors only.
# NumPy's eigensolver proposes integer witnesses; no eigenvalue decides a rejection.
import os,sys,itertools,time
os.environ["OPENBLAS_NUM_THREADS"]="1"
import numpy as np
from norm18_triple_core import partitions,leaflist,lab,tables,psd

from itertools import combinations as co, permutations as pe, product
from functools import lru_cache
from collections import Counter

@lru_cache(None)
def twocharts():
 keys=set()
 for p in partitions():
  for k in range(3):
   i,j=[h for h in range(3)if h!=k]
   for f,g in product(leaflist(p,i),leaflist(p,j)):
    def key(perm):
     e=lambda z:tuple(sorted(perm[h] for h in lab[z]))
     S=[]
     for u,F in [(i,f),(j,g)]:
      S.append(tuple(sorted((e(v),tuple(sorted(perm[q]for _,q,h in F if h==v)))for v in p[u])))
     return tuple(sorted(S)),tuple(sorted(e(v) for v in p[k]))
    keys.add(min(map(key,pe(range(4)))))
 return sorted(keys)
def small(ch):
 if isinstance(ch,tuple):
  ub,k=ch;return tri19(k,ub)[:3]
 groups,pk=twocharts()[ch]
 A=np.zeros((19,19),int)
 def e(i,j):A[i,j]=A[j,i]=1
 for q in range(1,5):e(0,q)
 for i,g in enumerate(groups):
  for l,(edge,leaves) in enumerate(g):
   v=5+2*i+l
   for q in edge:e(1+q,v)
   for h,q in enumerate(leaves):s=11+4*i+2*l+h;e(1+q,s);e(v,s)
 for l,edge in enumerate(pk):
  for q in edge:e(1+q,9+l)
 T=np.array([[1]+[-1]*4+[int(h//2!=i) for h in range(6)]+[int(h//4==i)for h in range(8)]for i in range(3)])
 return A,T,pk
@lru_cache(None)
def tabrow(ch,i):
 A,T,_=small(ch);c=[11+4*i+h for h in range(4)]+[5+h for h in range(6) if h//2!=i]
 F=12*np.eye(len(A),dtype=int)+2-A-A@A;opts=[]
 for S in co(range(8),4):
  sites=[c[h] for h in S];mask=sum(1<<s for s in sites)
  v=np.array([int(j in sites)for j in range(19)],int)
  if any(F[c[h],c[k]]<1 for h,k in co(S,2)) or (A@v+v).max()>2:continue
  opts.append((S,mask,v))
 R=[];cap=[[int(F[h,k])for k in c] for h in c]
 def go(start,uses,chosen,left):
  if left==0:
   if not any(uses):R.append(np.array([x[2]for x in chosen],int).T)
   return
  if max(uses)>left:return
  for ix in range(start,len(opts)):
   S,m,_=w=opts[ix]
   if any(uses[k]==0 for k in S) or any((m&k[1]).bit_count()>2 for k in chosen) or any(not cap[h][k]for h,k in co(S,2)):continue
   for k in S:uses[k]-=1
   for h,k in co(S,2):cap[h][k]-=1
   go(ix+1,uses,chosen+[w],left-1)
   for h,k in co(S,2):cap[h][k]+=1
   for k in S:uses[k]+=1
 go(0,[3]*4+[2]*4,[],5)
 return R
# A floating eigensolver may propose an integer negative witness; ONLY its exact
# quadratic form decides a rejection. Failure to find a witness retains the case.
def negproof(G):
 z,v=np.linalg.eigh(G)
 pick=np.flatnonzero(z[:,0]<-1.e-8)
 if not len(pick):return np.ones(len(G),bool)
 x=np.rint(1024*v[pick,:,0]).astype(np.int64)
 assert abs(x).max()<=1024 and (int(abs(G).max())*(1024*G.shape[1])**2)<2**62
 hit=np.einsum('ij,ijk,ik->i',x,G[pick],x)<0
 keep=np.ones(len(G),bool);keep[pick[hit]]=False
 return keep
def psbatch(A,T):
 n=T.shape[1];I=np.eye(n,dtype=int);s=T.sum(0)
 good=np.flatnonzero((12*I+2-A-A@A).min((1,2))>=0)
 for scale,G0 in ((-3168,9504*I+352-2016*T.T@T+441*np.outer(s,s)),(11,44*I-2)):
  if len(good):good=good[negproof(G0+scale*A[good])]
 return good
@lru_cache(None)
def Xtabs(r,c):
 T=tables(r,c);X=np.zeros((len(T),5,5),int)
 for ix,t in enumerate(T):
  for h,v in enumerate(t):X[ix,h,list(v)]=1
 return X
def base29(ch):
 A,T,pk=small(ch)
 if isinstance(ch,tuple):
  ub,k=ch;neg=tri19(k,ub)[3]
  if not len(psbatch(A[None,:,:],T)):return
 C=np.eye(19,dtype=int);E=12*C+2-A-A@A;G=[]
 for i in [0,1]:
  R=tabrow(ch,i)
  if isinstance(ch,tuple):
   rr=[]
   for old in R:
    for w in range(5):
     M=old.copy();M[neg[1-i],w]=1;rr.append(M)
   R=rr
  if not R:return
  Y=np.zeros((len(R),24,24),int);Y[:,:19,:19]=A;Y[:,:19,19:]=np.array(R);Y[:,19:,:19]=np.transpose(R,(0,2,1))
  Tg=np.concatenate((T,-np.eye(3,dtype=int)[:,[i]*5]),axis=1)
  G.append([R[v]for v in psbatch(Y,Tg)])
 T29=np.concatenate((T,-np.eye(3,dtype=int)[:,[0]*5+[1]*5]),axis=1)
 for M,N in product(*G):
  mn=M.T@N;X=Xtabs(tuple(T[1]@M),tuple(T[0]@N))
  if mn.max()>2 or not len(X) or (E-M@M.T-N@N.T).min()<0:continue
  X=X[((mn+X)<=2).all((1,2))&((A@M+M+N@X.transpose(0,2,1))<=2).all((1,2))&((A@N+N+M@X)<=2).all((1,2))]
  if not len(X):continue
  Y=np.zeros((len(X),29,29),int);Y[:,:19,:19]=A;Y[:,:19,19:24]=M;Y[:,:19,24:]=N;Y[:,19:24,:19]=M.T;Y[:,24:,:19]=N.T
  Y[:,19:24,24:]=X;Y[:,24:,19:24]=X.transpose(0,2,1)
  for y in psbatch(Y,T29):yield Y[y],T29,pk

@lru_cache(None)
def configs(es,ub):
 ed=tuple(sorted(es));qs=tuple(sorted([q for e in ed for q in e]));S=set()
 for v in set(pe(qs)):
  if ub:
   # B touches both, C,D touch one, E touches neither
   z=[(v[i],tuple(e for h,e in enumerate(ed)if ((3,1,2,0)[i]>>h)&1),i==3,i==0)for i in range(4)]
   if len({v[0],v[1],v[2]})<3:continue
   S.add((ed,tuple(sorted(z))))
  else:
   if v[0]==v[1] or v[2]==v[3]:continue
   for u in range(4):
    z=[(v[i],(ed[i//2],),i==u,i==u)for i in range(4)]
    S.add((ed,tuple(sorted(z))))
 return tuple(sorted(S))
@lru_cache(None)
def trgroup(s,p):
 es,Z=s;E=lambda e:tuple(sorted(p[t]for t in e))
 return tuple(sorted(E(e) for e in es)),tuple(sorted((p[q],tuple(sorted(E(e)for e in ee)),h,n) for q,ee,h,n in Z))
@lru_cache(None)
def trianglecharts(ub):
 S=set()
 for part in partitions():
  for k in range(3):
   i,j=[h for h in range(3)if k!=h];es=lambda i:tuple(sorted(lab[z]for z in part[i]))
   for g,h in product(configs(es(i),ub),configs(es(j),ub)):
    if (g,h) in S or (h,g) in S:continue
    orbit=[tuple(sorted((trgroup(g,p),trgroup(h,p))))for p in pe(range(4))]
    S.add(min(orbit))
 return sorted(S)
def tri19(ch,ub):
 g=trianglecharts(ub)[ch]; pk=tuple(sorted(set(lab)-set(g[0][0])-set(g[1][0])));A=np.zeros((19,19),dtype=int);pos=[];neg=[]
 def e(i,j):A[i,j]=A[j,i]=1
 for q in range(1,5):e(0,q)
 for i,(es,L) in enumerate(g):
  for h,ed in enumerate(es):
   for q in ed:e(1+q,5+2*i+h)
  for k,(q,ed,f,n) in enumerate(L):
   v=11+4*i+k;e(q+1,v)
   for d in ed:e(v,5+2*i+es.index(d))
   if f:pos.append(v)
   if n:neg.append(v)
 for k,e0 in enumerate(pk):
  for q in e0:e(1+q,9+k)
 e(*pos)
 T=np.array([[1]+[-1]*4+[int(h//2!=i) for h in range(6)]+[int(h//4==i)for h in range(8)]for i in range(3)])
 return A,T,pk,neg

@lru_cache(None)
def autos(ch):
 g,k=twocharts()[ch]; edge_to={ed:5+2*i+l for i,grp in enumerate(g)for l,(ed,L) in enumerate(grp)};edge_to.update({ed:9+l for l,ed in enumerate(k)})
 A,T,_=small(ch); R=[]
 for p in pe(range(4)):
  tr=lambda ed:tuple(sorted(p[h]for h in ed))
  moved=[tuple(sorted((tr(ed),tuple(sorted(p[v]for v in L)))for ed,L in grp))for grp in g]
  if sorted(moved)!=list(g) or sorted(tr(ed)for ed in k)!=list(k):continue
  pair=[g.index(v) for v in moved]; pos=[0]+[a+1 for a in p]+[0]*14
  for ed,v in edge_to.items():pos[v]=edge_to[tr(ed)]
  for i,grp in enumerate(g):
   for l,(ed,L) in enumerate(grp):
    j=pair[i];nxt=g[j];ll=next(h for h,(e,_)in enumerate(nxt)if e==tr(ed))
    for h,name in enumerate(L):pos[11+4*i+2*l+h]=11+4*j+2*ll+nxt[ll][1].index(p[name])
  assert np.array_equal(A[np.ix_(pos,pos)],A)
  R.append((np.argsort(pos),pair))
 return R
def dedup29(ch):
 seen=set()
 for A,T,pk in base29(ch):
  choices=[]
  for invp,move in autos(ch):
   old=sorted(range(2),key=lambda i:move[i])
   ids=[];bits=[]
   for i in old:
    B=A[invp,19+5*i:24+5*i] # full 19×5
    M=(2**np.arange(19))@B; ix=np.argsort(M)
    bits.extend(map(int,M[ix]));ids.append(19+5*i+ix)
   X=A[np.ix_(*ids)]
   choices.append(tuple(bits)+(int((2**np.arange(25))@X.ravel()),))
  key=min(choices)
  if key in seen:continue
  seen.add(key);yield A,T,pk

@lru_cache(None)
def abstract_y(ch):
 A,T,pk=small(ch)
 qs=sorted(q+1 for edge in pk for q in edge)
 opts={}
 for q in sorted(set(qs)):
  R=[]
  for l in range(3):
   for L in co([9,10],l):
    for g,h in product(range(5),repeat=2):
     # 0 or selected old private leaf
     F=(g!=0,h!=0); d=[l+f-1 for f in F]
     if min(d)<0 or max(d)>1:continue
     Z=[[None]if v==0 else range(19+5*i,24+5*i) for i,v in enumerate(d)]
     for n,m in product(*Z):
      sites=[q,*L]+([10+g] if g else [])+([14+h]if h else [])+[v for v in (n,m)if v is not None]
      R.append((sum(1<<v for v in sites),tuple(int(v)for v in (F[0],F[1],d[0],d[1],9 in L,10 in L)),tuple(sites),q))
  opts[q]=R
 return qs,opts
@lru_cache(None)
def sydata(ch):
 qs,opts=abstract_y(ch)
 R=sum((c for c in opts.values()),[])
 M=np.array([[int((r[0]>>h)&1) for h in range(29)]for r in R],int)
 pairs=list(co(range(29),2));tt=np.array([i for i,j in pairs]);uu=np.array([j for i,j in pairs])
 pairBad=(M[:,tt]&M[:,uu]);nullmask=np.array([r[0] for r in R],int);attr=np.array([r[1] for r in R],int);Q=np.array([r[3]for r in R])
 return qs,R,M,pairBad,tt,uu,nullmask,attr,Q
def fastY(ch,A,T):
 qs,R,M,M2,tt,uu,masks,attr,Q=sydata(ch)
 Ft=12*np.eye(29,dtype=int)+2-A-A@A
 cc=((M@A+M).max(1)<=2)&((M2@(Ft[tt,uu]==0))==0)
 for i in [0,1]:
  h=(T[i]==1).astype(int)@A
  if (h[T[i]==0]>3).any() or (h[T[i]==0]==3).sum()>1:return
  hp=M@(T[i]==1).astype(int);cc&=(hp<=(2 if (h[T[i]==0]==3).any() else 3))
 inds=np.flatnonzero(cc)
 if not len(inds):return
 Y=M[inds];I=np.eye(29,dtype=int);s=T.sum(0);Cs=[]
 h=(A+4*I)@T[2];db=14-A.sum(0)-h;BD=np.array([h,db]);Faug=np.block([[Ft,BD.T],[BD,np.array([[9,-8],[-8,77]])]])
 if not negproof(Faug[None,:,:])[0]:return
 tail=np.concatenate((Y,np.tile([-1,2],(len(Y),1))),axis=1)
 for G,B,d,k in [(Faug,tail,1,0),(9504*I+352-2016*T.T@T+441*np.outer(s,s)-3168*A,352-2016*T[2]+441*s-3168*Y,9504,-1223),(44*I+11*A-2,-2+11*Y,44,-2)]:
  # For each possible leaf, project a vector with leaf coordinate D to an integer
  # vector with first 29 coordinates -w. ANY w yields necessary Gram minors.
  ev,V=np.linalg.eigh(G);pos=ev>1.e-6;Vp=V[:,pos];V0=V[:,~pos]
  sol=((B@Vp/ev[pos])@Vp.T+100*(B@V0)@V0.T)
  D=np.clip(np.floor(32000/np.maximum(1,abs(sol).max(1))),1,1024).astype(np.int64)
  W=np.rint(np.clip(D[:,None]*sol,-32768,32768)).astype(np.int64)
  assert int(abs(W).max())<=32768 and 1<=D.min()<=D.max()<=1024
  maxw=int(abs(W).sum(1).max())
  assert int(abs(G).max())*maxw**2+2048*int(abs(B).max())*maxw+1024**2*(d+abs(k))<2**62
  WG=W@G;WB=W@B.T
  WB=WB*D[None,:];C=(WG@W.T)-(WB+WB.T)+np.outer(D,D)*k
  C[np.diag_indices(len(C))]+=D*D*d
  Cs.append(C)
 keep=np.flatnonzero(np.min([np.diag(C) for C in Cs],axis=0)>=0)
 if not len(keep):return
 idx=inds[keep];Q=Q[idx];at=attr[idx];ma=masks[idx]
 K=[C[np.ix_(keep,keep)].tolist()for C in Cs]
 ok=(M[idx]@M[idx].T<=1)
 for C in K:
  for i,v in enumerate(C):
   for j in range(i):
    if v[i]*C[j][j]<v[j]**2:ok[i,j]=ok[j,i]=False
 allowed=[np.flatnonzero(Q==q).tolist()for q in qs]
 if not all(allowed):return
 init=(1,1,1,1,2,2)
 at=at.tolist();ma=ma.tolist()
 def dfs(l,rem,chosen):
  if l==4:
   if any(rem)or Ft[9,10]-sum((ma[u]&1536)==1536 for u in chosen)>1:return
   if any(not psd([[C[u][v] for v in chosen] for u in chosen]) for C in K):return
   yield [ma[u] for u in chosen];return
  lo=chosen[-1] if l and qs[l-1]==qs[l] else -1
  for u in allowed[l]:
   if u<=lo or any(not ok[u,v]for v in chosen):continue
   rr=[x-y for x,y in zip(rem,at[u])]
   if min(rr)<0 or max(rr)>3-l:continue
   yield from dfs(l+1,rr,chosen+[u])
 yield from dfs(0,init,[])

def ok(a):
 return all((a[i]&a[j]).bit_count()+((a[i]>>j)&1)<=2 for i in range(len(a)) for j in range(i))
def addsite(a,v,w):
 # Add a new site with its prescribed lower-index neighbor mask.
 a=a[:]
 for h in range(len(a)):
  if w>>h&1:a[h]|=1<<v
 a[v]|=w
 return a
def end38(A,T):
 L=[(5,6),(7,8),(9,10)];Y=(29,30,31,32)

 Pm=[sum(1<<h for h in range(33) if t[h]==1)for t in T]
 Nm=[sum(1<<h for h in range(33) if t[h]==-1)for t in T]
 F=[[None if i==j else 2-(A[i]>>j&1)-(A[i]&A[j]).bit_count() for j in range(33)]for i in range(33)]
 H=[4*T[2][i]+(Pm[2]&A[i]).bit_count()-(Nm[2]&A[i]).bit_count() for i in range(33)]
 if min(H)<0 or max(H)>5:return
 used=[i for i in range(33) if H[i]]
 C=set(L[0]+L[1]+Y);rest=[i for i in used if i not in C]
 if any(T[2][i] for i in rest):return
 allow=[sum(1<<j for j in used if i!=j and F[i][j]>0) for i in range(33)]
 cones=[A[i]|(1<<i) for i in range(33)]
 def feasible(w,h):
  return all((w&cones[j]).bit_count()<=2 for j in range(33) if cones[j]>>h&1)
 def words(w,U):
  if all((w&p).bit_count()==(w&m).bit_count()<=3 for p,m in zip(Pm[:2],Nm[:2])):
   yield w
  while U:
   bit=U&-U;U-=bit;j=bit.bit_length()-1
   ww=w|bit
   if feasible(ww,j):yield from words(ww,U&allow[j])
 R=[]
 for cc in co(sorted(C),4):
  if any(not H[j] for j in cc):continue
  w=sum(1<<j for j in cc)
  if any((w&allow[j]).bit_count()!=3 or not feasible(w,j) for j in cc):continue
  U=sum(1<<j for j in rest)
  for j in cc:U&=allow[j]
  R+=list(words(w,U))
 # cap incidence for the two endpoint omitted center pairs (at most one exterior common neighbor).
 req={tuple(L[i]):F[L[i][0]][L[i][1]] for i in [0,1]}
 def complete(W):
  if any(v-sum((w>>j)&(w>>k)&1 for w in W) not in (0,1) for (j,k),v in req.items()):return
  a=A[:]
  for s,w in zip(range(33,38),W):a=addsite(a,s,w)
  if ok(a):yield a
 def go(h,U,W):
  if len(W)==5:
   if not any(h):yield from complete(W)
   return
  if any(t>5-len(W) for t in h):return
  zero=sum(1<<i for i,z in enumerate(h) if z==0)
  U=[r for r in U if not r&zero]
  by={i:[w for w in U if w>>i&1] for i in used if h[i]}
  if not by or any(len(rs)<h[i] for i,rs in by.items()):return
  from math import comb
  i=min(by,key=lambda j:comb(len(by[j]),h[j]))
  for S in co(by[i],h[i]):
   if any((w&y).bit_count()>2 for w,y in co(S,2)):continue
   H1=[t-sum(w>>j&1 for w in S) for j,t in enumerate(h)]
   if min(H1)<0:continue
   V=[w for w in U if not(w>>i&1) and all((w&y).bit_count()<=2 for y in S)]
   yield from go(H1,V,W+S)
 yield from go(H,R,())


def core33(A,T,Y):
 a=[sum(1<<int(j) for j in np.flatnonzero(r))for r in A]+[0]*9
 for j,m in enumerate(Y):a=addsite(a,29+j,m)
 if not ok(a):return
 t=[r+[0 if j!=2 else 1]*4 for j,r in enumerate(T.tolist())]
 yield from end38(a,t)

def run(ch):
 R=[0,0,0,0]
 for A,T,pk in (base29(ch) if isinstance(ch,tuple) else dedup29(ch)):
  R[0]+=1
  for yy in fastY(ch,A,T):
   if isinstance(ch,tuple) and ch[0]:
    g=trianglecharts(ch[0])[ch[1]]
    if any(any((mask>>(11+4*i+j))&1 for mask in yy) for i in (0,1)
           for j,(q,cent,f,n) in enumerate(g[i][1]) if not f):continue
   R[1]+=1
   for a in core33(A,T,yy):
    R[2]+=1;N=np.array([[(m>>j)&1 for j in range(38)]for m in a])
    TT=np.concatenate((T,np.eye(3,dtype=int)[:,[2]*4],-np.eye(3,dtype=int)[:,[2]*5]),axis=1)
    if len(psbatch(np.array([N]),TT)):
     F=12*np.eye(38,dtype=int)+2-N-N@N;d=14-N.sum(0)
     if psd(61*F-np.outer(d,d)):
      R[3]+=1;print('SURVIVING CORE:',ch,a,flush=True)
 sydata.cache_clear();abstract_y.cache_clear();tabrow.cache_clear()
 return R
if __name__=='__main__':
 for case in ([sys.argv[1]] if len(sys.argv)>1 else ['path','balanced','unbalanced']):
  assert case in ('path','balanced','unbalanced')
  ub=(case=='unbalanced')
  n=(len(twocharts()) if case=='path' else len(trianglecharts(ub)))
  assert n=={'path':26,'balanced':258,'unbalanced':199}[case]
  ids=list(map(int,sys.argv[2:])) or list(range(n));assert all(0<=j<n for j in ids)
  cc=[0]*4
  for j in ids:
   r=run(j if case=='path' else (ub,j));cc=[v+w for v,w in zip(cc,r)]
   print(case,j,*r,flush=True)
  print('TOTAL',case,len(ids),*cc,flush=True)
  assert cc[-1]==0,"a fully necessary 38-site core remains"
