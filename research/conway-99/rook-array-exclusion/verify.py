from itertools import permutations,product,combinations
from collections import defaultdict,Counter
P=list(permutations(range(3))); MUL=[[P.index(tuple(p[q[i]] for i in range(3))) for q in P] for p in P];iv=[w.index(0) for w in MUL]
def norm(g):
 return tuple(MUL[MUL[iv[g[0][c]]][g[r][c]]][MUL[iv[g[r][0]]][g[0][0]]] for r,c in ((1,1),(1,2),(2,1),(2,2)))
def sym(t):
 a,b,c,d=t;g=[[0,0,0],[0,a,b],[0,c,d]];o=set()
 for h in (g,[[iv[g[j][i]] for j in range(3)] for i in range(3)]):
  for rp in P:
   for cp in P:
    z=norm([[h[i][j] for j in cp] for i in rp])
    for k in range(6):o.add(tuple(MUL[MUL[k][x]][iv[k]] for x in z))
 return o
def reps():
 seen=set()
 for t in product(range(6),repeat=4):
  if t not in seen:
   o=sym(t);seen.update(o);yield t,len(o)
def mask(v):return sum(1<<i for i in v)
def bits(z):
 while z:
  m=z&(-z);yield m.bit_length()-1;z-=m
def core(t):
 a,b,c,d=t;g=[[0,0,0],[0,a,b],[0,c,d]];A=[0]*27
 for x,y in combinations(range(27),2):
  i,z=divmod(x,3);j,w=divmod(y,3);r,c=divmod(i,3);s,f=divmod(j,3)
  if i==j or r==s and z==w or c==f and P[g[r][c]][z]==P[g[s][f]][w]:A[x]|=1<<y;A[y]|=1<<x
 return A
def srcheck(A):
 if any((A[i]&A[j]).bit_count()>2-(A[i]>>j&1) for i,j in combinations(range(27),2)):return 'srg'
 tr=[(mask((i,j,k)),(i,j,k)) for i,j,k in combinations(range(27),3) if (A[i]>>j)&(A[i]>>k)&(A[j]>>k)&1];assert len(tr)==27
 gs=set()
 for ti,(m,v) in enumerate(tr):
  for si,(n,w) in enumerate(tr[:ti]):
   if m&n:continue
   es=[(i,j) for i in v for j in w if A[i]>>j&1]
   if len(es)!=3:continue
   caps=[(A[i]&A[j]).bit_length()-1 for i,j in es];assert all((A[i]&A[j]).bit_count()==1 for i,j in es)
   if not all(A[i]>>j&1 for i,j in combinations(caps,2)):continue
   gs.add(m|n|mask(caps))
 return gs,tr
def arrays(A,p,grids):
 vs=[tuple(3*(3*r+c)+j for j in range(3)) for r,c in enumerate(p)]
 R=[[[2-(A[i]&A[j]).bit_count() for j in vs[v]] for i in vs[u]] for u,v in ((0,1),(0,2),(1,2))]
 X=[];sol=[];T=[]
 for i,j in product(range(3),repeat=2):
  wh=[k for k in range(3) if all((g&mask((vs[0][i],vs[1][j],vs[2][k]))).bit_count()==1 for g in grids)]
  T.append((i,j,tuple(combinations(wh,R[0][i][j]))))
 T.sort(key=lambda q:len(q[2]))
 def rec(s):
  if s==9:
   assert len(X)==12 and not any(any(r) for mat in R[1:] for r in mat);sol.append(tuple(X));return
  i,j,js=T[s]
  for gs in js:
   if not all(R[1][i][k]>0 and R[2][j][k]>0 for k in gs):continue
   for k in gs:R[1][i][k]-=1;R[2][j][k]-=1;X.append(mask((vs[0][i],vs[1][j],vs[2][k])))
   rec(s+1)
   for k in gs:R[1][i][k]+=1;R[2][j][k]+=1;X.pop()
 rec(0);return sol
CT=((0,1,2,3),(0,1,3,2),(1,2,2,1),(1,2,3,5),(3,4,4,3))
def check():
 st=Counter();ss=[]
 for t,w in reps():
  A=core(t);g=srcheck(A)
  if isinstance(g,str):st[g]+=w;continue
  a=[len(arrays(A,p,g[0])) for p in P]
  if not min(a):st['noarray']+=w;continue
  st['remaining']+=w;ss.append((t,w,tuple(a)))
 assert list(t for t,w,a in ss)==list(CT)
 assert st==Counter(noarray=880,remaining=416)
 print(st,ss)
def isos(A):
 edges=[(i,j) for i in range(9) for j in range(9) if i!=j and (i//3==j//3 or i%3==j%3)]
 M={(i,j):P.index(tuple(next(z for z in range(3) if A[3*i+w]>>(3*j+z)&1) for w in range(3))) for i,j in edges};out=[]
 for tr in (0,1):
  for r,c in product(P,repeat=2):
   cc=[(c[j]*3+r[i] if tr else r[i]*3+c[j]) for i,j in product(range(3),repeat=2)]
   for p in range(6):
    eta={0:p};ok=True
    for i in range(9):
     for j in range(9):
      if (i,j) not in M or i not in eta:continue
      q=MUL[MUL[M[cc[i],cc[j]]][eta[i]]][iv[M[i,j]]]
      if j in eta and q!=eta[j]:ok=False;break
      eta[j]=q
     if not ok:break
    if ok:out.append(tuple(3*cc[j]+P[eta[j]][w] for j in range(9) for w in range(3)))
 return out
def tables(t):
 A=core(t);gr,tr=srcheck(A);arr=[arrays(A,p,gr) for p in P];fl=[sum(map(list,f),[]) for f in product(*arr)]
 lookup={tuple(sorted(v)):i for i,v in enumerate(fl)};wr=set(x for v in fl for x in v)
 MS=[{x:mask(perm[j] for j in bits(x)) for x in wr} for perm in isos(A)];seen=set();out=[]
 for i,v in enumerate(fl):
  if i not in seen:
   ob={lookup[tuple(sorted(M[x] for x in v))] for M in MS};seen.update(ob);out.append((i,len(ob),v))
 return out
from math import comb
from time import monotonic
def rows(A,ws,y,allowed=None):
 W=ws[y];b=[2-((W>>j)&1)-(A[j]&W).bit_count() for j in range(27)]
 cand=[j for j,z in enumerate(ws) if y!=j and (z&W).bit_count()<=1 and not any(z>>i&1 and b[i]==0 for i in range(27)) and (allowed is None or (allowed[y]>>j&1))]
 m=[z|(1<<(27+i//12)) for i,z in enumerate(ws)]
 cv=[mask(j for j in cand if m[j]>>k&1) for k in range(33)];out=[];q=y//12
 parity=[p==P[q] or sum(u==v for u,v in zip(p,P[q]))==0 for p in P]
 def rec(cand,r,sol):
  best=None;pen=1<<75
  for i,n in enumerate(r):
   if not n:continue
   ns=cand&cv[i];s=ns.bit_count()
   if s<n:return
   cost=comb(s,n)
   if cost<pen:pen=cost;best=(i,n,ns)
  if best is None:
   assert sol.bit_count()==11;out.append(sol);return
  assert best is not None
  i,n,ns=best;V=cand^ns
  for js in combinations(bits(ns),n):
   r2=r.copy();s=V;ok=True
   for j in js:
    for k in bits(m[j]):
     r2[k]-=1
     if r2[k]<0:ok=False;break
     if not r2[k]:s&=~cv[k]
    if not ok:break
   if ok:rec(s,r2,sol|mask(js))
 for v in range(4):
  r=b+[(4-v-(j==q)) if parity[j] else v for j in range(6)]
  ss=mask(cand)
  for j,n in enumerate(r):
   if not n:ss&=~cv[j]
  rec(ss,r,0)
 return sorted(set(out))
def clique(t,idx,budget=0,audit=False):
 import numpy as np
 A=core(t);ww=next(w for i,wt,w in tables(t) if i==idx);allow=None
 L=[rows(A,ww,i,allow) for i in range(72)];D=[len(x) for x in L]
 print('table',t,idx,'domains',min(D),sum(D),max(D),flush=True)
 R=[(np.array([z&((1<<64)-1) for z in row],dtype='uint64'),np.array([z>>64 for z in row],dtype='uint64')) for row in L]
 caps=[[2-(u&v).bit_count() for v in ww] for u in ww]
 memo={};N=0;start=monotonic();ext=[];ctr=Counter()
 def comp(i,h,j):
  ky=i,h,j
  if ky in memo:return memo[ky]
  grp=R[j];z=L[i][h];adj=(z>>j)&1;req=caps[i][j]-adj
  if req<0:return 0
  eq=(grp[i//64]>>(i%64))&1
  val=np.bitwise_count(grp[0] & np.uint64(z&((1<<64)-1)))+np.bitwise_count(grp[1] & np.uint64(z>>64))
  v=int.from_bytes(np.packbits((eq==adj)&(val==req),bitorder='little').tobytes(),'little')
  if audit:assert v==sum(1<<l for l,y in enumerate(L[j]) if (y>>i)&1==adj and (z&y).bit_count()==req)
  if len(memo)<1500000:memo[ky]=v
  return v
 def search(ss):
  nonlocal N
  N+=1
  assert not budget
  if not ss:return tuple(ext)
  i=min(ss,key=lambda j:ss[j].bit_count());ds=ss[i];ctr[len(ext)]+=1
  for h in bits(ds):
   tt={};ok=True
   for j,x in ss.items():
    if j==i:continue
    v=x&comp(i,h,j)
    if not v:ok=False;break
    tt[j]=v
   if ok:
    ext.append((i,h));z=search(tt)
    if z is not False:return z
    ext.pop()
  return False
 res=search({i:(1<<n)-1 for i,n in enumerate(D)})
 print('CSP',t,idx,'nodes',N,'seconds',round(monotonic()-start,2),'states',len(memo),'hist',sorted(ctr.items()),'answer',str(res)[:20],flush=True)
 return res

if __name__=='__main__':
 import argparse,os,sys,time,platform,hashlib,numpy
 p=argparse.ArgumentParser()
 p.add_argument('--branch',type=int,choices=range(5))
 p.add_argument('--table',type=int)
 p.add_argument('--shard',type=int,default=0)
 p.add_argument('--shards',type=int,default=1)
 p.add_argument('--audit',action='store_true')
 v=p.parse_args();assert 0<=v.shard<v.shards
 print('Python',platform.python_version(),'NumPy',numpy.__version__,'shard',v.shard,'/',v.shards,flush=True)
 start=time.monotonic();cpu=time.process_time();check();n=ix=0
 for k,t in enumerate(CT):
  tb=tables(t);assert len(tb)==[2,21,51,6,6][k]
  for i,w,ws in tb:
   select=ix%v.shards==v.shard and (v.branch is None or v.branch==k) and (v.table is None or v.table==i);ix+=1
   if not select:continue
   tic=time.monotonic();pp=time.process_time()
   assert clique(t,i,audit=v.audit) is False
   print('END',t,'id',i,'multiplicity',w,'wall',round(time.monotonic()-tic,4),'cpu',round(time.process_time()-pp,4),flush=True)
   n+=1
 assert ix==86
 if v.branch is None and v.table is None:assert n==len(range(v.shard,86,v.shards))
 print('EXACT REJECTIONS',n,'wall',round(time.monotonic()-start,4),'cpu',round(time.process_time()-cpu,4),flush=True)
