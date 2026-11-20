"""Independent integer generator. No optimizer is used in this module."""
import itertools as it
from functools import lru_cache
import numpy as np
from scipy.sparse import csr_matrix, coo_matrix
P=list(it.combinations(range(7),2))
W=[(a,b) for a,b in it.combinations(range(12),2) if a//2!=b//2]
def check(test,text):
 if not test:raise ValueError(text)
def cell(a,b):return P.index(tuple(sorted((int(a),int(b)))))
def wing(i,j):return 3+12*i+j
def frame(tw):
 N=[set() for j in range(39)]
 def edge(a,b):N[a].add(b);N[b].add(a)
 for i in range(3):
  j=(i+1)%3;edge(i,j)
  for u in range(12):
   v=u
   if i==2 and u<6:v=2*((u//2+1)%3)+((u%2)^(tw if u>=4 else 0))
   edge(i,wing(i,u));edge(wing(i,u),wing(j,v))
   if u%2==0:edge(wing(i,u),wing(i,u+1))
 return N
def specs(t):
 # Independent actual shell relabelings. On defect cycles find lift by BFS over
 # neighbor colors (transfer +/- and mate). Verify each permutation on all edges.
 N=frame(t);actions=[]
 for s in (1,-1):
  for a in range(9):
   images={i:(s*i+a)%3 for i in range(3)}
   for i in range(3):
    for z in range(6,12):images[wing(i,z)]=wing(images[i],z)
   n=18 if t else 9
   for pos in range(18):
    i=pos%3;g=(pos//3)%3;bit=pos//9
    dest=(s*pos+a)%n+(9*bit if not t else 0);im=wing(dest%3,2*((dest//3)%3)+dest//9)
    images[wing(i,2*g+bit)]=im
   check(len(set(images.values()))==39 and all({images[x]for x in N[y]}==N[images[y]] for y in range(39)),'invalid frame symmetry')
   actions.append(images)
 rem=set(it.product(range(4),repeat=3));out=[]
 while rem:
  v=min(rem);orb=set()
  for pi in actions:
   q=[0]*3
   for i,j in enumerate(v):
    if j:q[pi[i]]=1+(pi[wing(i,2*(j-1))]-3)%12//2
   orb.add(tuple(q))
  check(orb<=rem,'overlap');rem-=orb;out.append((v,len(orb)))
 check(sorted(k for v,k in out)==[1]+[9]*7,'wrong orbit sizes')
 return out
@lru_cache(None)
def states(t):
 D=[(a,b)for a in (3,4,5,6)for b in (0,1,2)]
 if t:D.extend((t-1,b)for b in (0,1,2)if b!=t-1)
 # Enumerate each source's incident ternary row, retaining sum zero at both ends.
 sources=sorted({a for a,b in D});heads=sorted({b for a,b in D})
 local={a:[(ff,c) for ff in [[(b,cell(a,b))for x,b in D if x==a]] for c in it.product((-1,0,1),repeat=len(ff)) if sum(c)==0]for a in sources}
 flows=[]
 for parts in it.product(*(local[a]for a in sources)):
  row=[0]*21;total=[0]*7
  for ff,cs in parts:
   for (b,h),v in zip(ff,cs):row[h]=v;total[b]+=v
  if all(total[b]==0 for b in heads):flows.append(tuple(row))
 directed={cell(a,b):(a,b)for a,b in D};res=[]
 for h,f in enumerate(P):
  for row in flows:
   if h in directed and row[h]!=-1:continue
   def valid(e):
    if e==h or set(f).isdisjoint(P[e]):return True
    if h in directed and(directed[h][0]==directed[e][0] or directed[h][1]==directed[e][1]):return row[e]>=0
    return row[e]==0
   if not all(valid(e)for e in directed):continue
   deg=tuple(2*(h==e)+int(set(f).isdisjoint(g))+row[e]for e,g in enumerate(P))
   partner=tuple((1 if h in directed else 2) if h==e else (row[e] if h in directed and e in directed and directed[h][1]==directed[e][1] else 0)for e in range(21))
   res.append((h,row,deg,partner))
 return directed,res
def words(N):
 # 60^3 triples. Each footprint records local sites as vertex numbers 3,...,38.
 choices=np.array([[wing(i,j)for i,p in enumerate(ps)for j in p]for ps in it.product(W,repeat=3)],dtype=np.int16)
 adj=np.array([[int(j in N[i])for j in range(39)]for i in range(39)],dtype=np.int64)
 r=2-adj-adj@adj;ok=np.ones(len(choices),bool)
 for j,k in it.combinations(range(6),2):ok &= r[choices[:,j],choices[:,k]]>0
 for j in range(6):ok &= adj[choices[:,j,None],choices].sum(1)<=1
 for g in (3,4,5):ok &= (((choices-3)%12//2)==g).sum(1)==1
 return choices[ok],adj,r
def groups(N,V):
 # permutations and sign reversals of three globally fixed pairs, simultaneously in all arms.
 lookup={tuple(row):j for j,row in enumerate(V)};acts=[]
 for pp in it.permutations((3,4,5)):
  for bits in it.product((0,1),repeat=3):
   ax=[0,1,2,*pp,6];pi=list(range(39))
   for i in range(3):
    for j in range(6,12):pi[wing(i,j)]=wing(i,2*ax[j//2]+((j%2)^bits[j//2-3]))
   check(all({pi[v]for v in N[y]}==N[pi[y]]for y in range(39)),'fixed group')
   pv=np.sort(np.asarray(pi)[V].reshape(-1,3,2),axis=2).reshape(-1,6)
   fp=np.array([lookup[tuple(r)]for r in pv]);acts.append((ax,pi,fp))
 return acts
class Physical:
 def __init__(self,i,t,N,V,adj):
  self.i=i;self.directed,self.states=states(t);dr=self.directed;st=self.states
  self.adj=adj;self.near=near=[v for v in range(3,39)if (v-3)//12!=i]
  ing=N[i]-set(range(3));self.parents=par=[tuple(sorted(N[v]&N[i]))for v in near]+[tuple(row[2*i:2*i+2])for row in V]
  def axis(p):return (p-3)%12//2 if p>=3 else 6
  self.cells=hc=np.array([cell(*(axis(p)for p in parents))for parents in par])
  nearby=np.zeros((len(par),39),np.int8);nearby[:24]=adj[near];np.put_along_axis(nearby[24:],V,1,axis=1);self.J=nearby
  self.parbits=pb=np.zeros((len(par),39),bool);np.put_along_axis(pb,np.array(par),True,axis=1)
  # Use signed-parent internal-flip rule, on far words only. A required far
  # partner cannot instead be an adjacent chosen point of the 39-shell.
  ok=np.ones(len(par),bool)
  for j in (0,1):
   a=V[:,2*i+j];must=np.array([h not in dr or dr[h][0]==axis(p)for h,p in zip(hc[24:],a)])
   ok[24:] &= ~(must & (adj[a[:,None],V].sum(1)>0))
  # Candidate state decided using known neighbors in all six cells meeting T.
  hs=[cell(a,6)for a in range(6)];by={}
  for k,(h,r,d,p)in enumerate(st):by.setdefault((h,*(d[u]for u in hs)),[]).append(k)
  known=np.column_stack([nearby[:,np.array(near)[hc[:24]==u]].sum(1)for u in hs])
  fibers=[by.get((h,*ds),()) if b else () for h,ds,b in zip(hc,known,ok)]
  self.ph=np.repeat(np.arange(len(par)),[len(f)for f in fibers]);self.st=np.fromiter(it.chain.from_iterable(fibers),int)
  self.g=np.array([d for h,r,d,p in st],np.int8);self.j=np.array([p for h,r,d,p in st],np.int8)
 def reduce(self,acts):
  st=self.states;ps=self.ph;ss=self.st;n=len(st);nidx={v:j for j,v in enumerate(self.near)};sl={(h,r):k for k,(h,r,d,p)in enumerate(st)};idx={int(v):k for k,v in enumerate(ps*n+ss)};rep=np.arange(len(ss))
  for ax,pi,fp in acts:
   col=[cell(ax[a],ax[b])for a,b in P];back=np.argsort(col)
   state=np.array([sl[col[h],tuple(r[j]for j in back)]for h,r,d,p in st]);physical=np.r_[[nidx[pi[z]]for z in self.near],fp+24]
   keys=physical[ps]*n+state[ss];rep=np.minimum(rep,np.fromiter((idx[int(z)]for z in keys),int))
  return np.unique(rep,return_inverse=True)[1]
class Rows:
 def __init__(self,n):self.n=n;self.rows=[];self.q=[];self.ids=[]
 def add(self,js,cs,rhs,name):
  # exact signed integer accumulation by quotient-variable index
  cs=np.asarray(cs,dtype=np.int64);out=np.zeros(self.n,np.int64);np.add.at(out,js,cs)
  sel=np.flatnonzero(out)
  if len(sel)==0 and rhs==0:return
  self.rows.append((sel,out[sel]));self.q.append(rhs);self.ids.append(name)
 def matrix(self):
  nj=len(self.rows);data=np.concatenate([v for j,v in self.rows]);cols=np.concatenate([j for j,v in self.rows]);ptr=np.cumsum([0]+[len(j)for j,v in self.rows])
  return csr_matrix((data,cols,ptr),shape=(nj,self.n)),np.array(self.q,np.int64)
def build(tw,sp):
 N=frame(tw);V,adj,r=words(N);check(len(V)==12096,'raw count')
 mask=np.ones(len(V),bool)
 for i,t in enumerate(sp):
  v=Physical(i,t,N,V,adj);mask &= np.bincount(v.ph,minlength=24+len(V))[24:]>0
 V=V[mask];acts=groups(N,V);phys=[Physical(i,t,N,V,adj)for i,t in enumerate(sp)]
 rep=np.minimum.reduce([f for a,p,f in acts]);xr,zid=np.unique(rep,return_inverse=True);nf=len(xr)
 yy=[s.reduce(acts)for s in phys];off=np.cumsum([nf]+[max(y)+1 for y in yy]);eq=Rows(off[-1]);ub=Rows(off[-1])
 # Keep one representative relation per H-orbit wherever this is elementary;
 # extra retained rows need not be independent.
 for i in range(3):
  for a,b in W:
   p,q=wing(i,a),wing(i,b);js=np.flatnonzero((V[:,2*i]==p)&(V[:,2*i+1]==q));eq.add(zid[js],1,1,('wing',i,a,b))
 for i,j in it.combinations(range(3),2):
  for a,b in it.product(range(12),repeat=2):
   p,q=wing(i,a),wing(j,b);js=np.flatnonzero((V[:,2*i:2*i+2]==p).any(1)&(V[:,2*j:2*j+2]==q).any(1))
   eq.add(zid[js],1,r[p,q],('cross',p,q))
 for i,(s,ids)in enumerate(zip(phys,yy)):
  ys=off[i]+ids;np0=s.ph;st=s.st;hc=s.cells;ownidx=[np.flatnonzero(np0==j)for j in range(24)]
  for j in range(24):eq.add(ys[ownidx[j]],1,1,('near-sum',i,j))
  for j in xr:
   js=ys[np0==j+24];eq.add(np.r_[zid[j],js],np.r_[-1,np.ones(len(js),int)],0,('far-link',i,int(j)))
  for k,p in enumerate(s.near):
   sel=np.flatnonzero(s.J[np0,p]);pt=s.ph[sel];own=ownidx[k];shared=s.parbits[pt][:,s.parbits[k]].any(1);z=st[sel]
   for h,f in enumerate(P):
    if 6 in f:continue
    js=sel[hc[pt]==h]
    eq.add(np.r_[ys[js],ys[own]],np.r_[np.ones(len(js),int),-s.g[st[own],h]],0,('exact-deg',i,p,h))
    if not set(f).isdisjoint(P[hc[k]]):continue
    covered=(hc[pt]==h).astype(int)+s.j[z,h]+shared*s.g[z,h]
    ub.add(ys[sel],-covered,-4,('point-H',i,p,h))
 A,b=eq.matrix();U,q=ub.matrix()
 # Repeated quotient rows from the same orbit are redundant. Dedup by their
 # full signed coefficient vector and RHS in insertion order.
 def dedup(M,b,ids):
  keep=[];seen=set()
  for i,bb in enumerate(b):
   l,r=M.indptr[i:i+2];key=(int(bb),M.indices[l:r].tobytes(),M.data[l:r].tobytes())
   if key not in seen:keep.append(i);seen.add(key)
  return M[keep],b[keep],[ids[i]for i in keep]
 A,b,eids=dedup(A,b,eq.ids);U,q,uids=dedup(U,q,ub.ids)
 return A,b,U,q,eids,uids
if __name__=='__main__':
 import sys,time
 for tw in range(2):print(tw,specs(tw),flush=True)
 t=time.time();A,b,U,q,*_=build(0,(1,2,1));print(A.shape,U.shape,time.time()-t)
