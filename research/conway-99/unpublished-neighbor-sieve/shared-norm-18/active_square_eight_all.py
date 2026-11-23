"""Exact enumerator using only integer sets and bitwise counts."""
import numpy as np,itertools as it,sys,time

from functools import cache
if len(sys.argv)!=2:raise SystemExit("argument: one partition of 6 in descending order, e.g. 3,2,1")
parts=tuple(map(int,sys.argv[1].split(',')))
expected={(6,):19,(5,1):20,(4,2):17,(4,1,1):16,(3,3):8,(3,2,1):22,(3,1,1,1):12,(2,2,2):5,(2,2,1,1):11,(2,1,1,1,1):8,(1,1,1,1,1,1):2}
assert parts in expected
t0=time.time()
S=range(12);l=lambda i:i^1
size={};block={};starts=[];pos=0
for k in parts:
 starts.append(pos)
 for i in range(pos,pos+2*k):size[i]=2*k;block[i]=pos
 pos+=2*k
def r(i):return block[i]+(i-block[i]+(1 if i%2 else -1))%size[i]
def perm(I,J):
 # canonical ordered source pair I,J for the color-preserving relabeling group;
 # returns (target indices, a permutation mapping I,J onto them)
 s,t=block[I],block[J]; Bs={w:[b for b in starts if size[b]==w]for w in set(size.values())}
 u=Bs[size[I]][0]
 if s==t:v=u
 else:v=next(b for b in Bs[size[J]] if b!=u)
 bm={s:u,t:v}
 for olds in Bs.values():
  av=iter(sorted(set(olds)-set(bm.values())))
  for b in olds:
   if b not in bm:bm[b]=next(av)
 def f(h):
  b=block[h];x=h-b;n=size[h]
  src=I if b==s else J if b==t else b
  return bm[b]+(((1 if src%2==0 else -1)*(h-src))%n)
 g=tuple(map(f,S))+(12,13)
 assert sorted(g)==list(range(14)) and all(g[l(x)]==l(g[x]) and g[r(x)]==r(g[x])for x in S)
 return g[I],g[J],g
a=12;z=13;mate=lambda i:25-i if i>=12 else l(i)
tags=[(i,j)for i in range(14)for j in range(i+1,14)if mate(i)!=j]; ids={x:i for i,x in enumerate(tags)}
def mask(ed):return sum(1<<ids[tuple(sorted(pair))] for pair in set(tuple(sorted(x))for x in ed))
def bmask(X):return sum(1<<i for i in X)
def gen(i):
 for xt in it.combinations(S,5):
  X=set(xt)
  if not {i,l(r(i)),r(l(i))}<=X or any(l(j)in X or r(j)in X for j in X):continue
  A=[z,*xt];B=[mate(x)for x in A];O=sorted(set(S)-set(A)-set(B)); U=sorted(X-{i})
  cut=[(k,j)for k in [z,i]for j in U]
  for b in it.permutations([v for v in B if v!=r(i)]):
   if any(t==mate(k)for k,t in zip(xt,b)):continue
   base=[(z,r(i)),*zip(xt,b)];tau=xt[b.index(a)]
   for jj in [1,2,3]:
    Y=U.copy();h=Y.pop(jj);j=Y.pop(0);add=[(h,j),tuple(Y)]; F=mask(cut+base+add)
    for f in it.combinations(U,2):
     E=[(O[0 if j in f else 1],mate(j))for j in U]
     yield bmask(X),tau,mask(base+add+E),F

def uf(v):return np.uint64(v)
stop=(1<<64)-1
def raw(i):
 b=list(gen(i));assert len(b)==len(set(b))
 return np.array([(x,t,w&stop,w>>64,f&stop,f>>64,c&stop,c>>64)for x,t,w,f in b for c in [mask([(q,j)for q in (z,i)for j in S if j!=i and x>>j&1])]],dtype=np.uint64).T.copy()
RR=[raw(i)for i in S]
assert len(tags)==84
XCOUNTS={(6,):[6]*12,(5,1):[7]*10+[25]*2,(4,2):[6]*8+[16]*4,
 (4,1,1):[8]*8+[34]*4,(3,3):[9]*12,(3,2,1):[10]*6+[20]*4+[26]*2,
 (3,1,1,1):[12]*6+[44]*6,(2,2,2):[16]*12,(2,2,1,1):[24]*8+[36]*4,
 (2,1,1,1,1):[32]*4+[56]*8,(1,1,1,1,1,1):[80]*12}
assert all(rr.shape==(8,954*d)for rr,d in zip(RR,XCOUNTS[parts]))
print('rows',[v.shape[1] for v in RR],time.time()-t0,flush=True)
def matrix(i,j):
 x=RR[i];y=RR[j];nn=x.shape[1];mm=y.shape[1];B=np.zeros((nn,(mm+7)//8),np.uint8);pc=np.bitwise_count
 adj=int(r(i)==j)
 c=lambda a,b:pc(a[0]&b[0])+pc(a[1]&b[1])
 gs=lambda a:[(int(w),np.where(a[0]==w)[0])for w in np.unique(a[0])]
 yg=gs(y)
 for X,ix in gs(x):
  t=np.zeros((len(ix),mm),bool);src=x[:,ix]
  b=bool((X>>j&1)|adj)
  for Y,jx in yg:
   if X==Y:continue
   a=bool((Y>>i&1)|adj);dst=y[:,jx]
   ii=np.flatnonzero((c(src[2:4],dst[6:8,:1])==2*(not a))&((src[1]!=j)|bool(Y>>i&1)))
   if not len(ii):continue
   jj=np.flatnonzero((c(dst[2:4],src[6:8,:1])==2*(not b))&((dst[1]!=i)|bool(X>>j&1)))
   if not len(jj):continue
   xx=src[:,ii,None];yy=dst[:,None,jj]
   ok=(xx[1]!=yy[1])&(c(xx[2:4],yy[2:4])==1-adj)&(c(xx[2:4],yy[4:6])==3*(not a))&(c(xx[4:6],yy[2:4])==3*(not b))
   t[np.ix_(ii,jx[jj])]=ok
  B[ix]=np.packbits(t,axis=1,bitorder='little')
 return B
# Map an entire row tensor by a permutation, using byte tables for 84-bit masks.
@cache
def remap(i,h,g):
 if all(g[x]==x for x in S):return np.arange(RR[i].shape[1],dtype=int)
 a=RR[i];z=np.empty_like(a);sl=RR[h];
 lx=np.array([sum(1<<g[q] for q in S if k>>q&1) for k in range(4096)],dtype=np.uint64)
 z[0]=lx[a[0]];z[1]=np.array(g,dtype=np.uint64)[a[1]]
 d=[ids[tuple(sorted((g[v],g[w])))]for v,w in tags]
 for k in (2,4,6):
  z[k:k+2]=0
  for b in range(0,84,8):
   s=d[b:b+8];tab=[sum(1<<s[j] for j in range(len(s)) if v>>j&1)for v in range(256)]
   arg=(a[k+b//64]>>uf(b%64))&255
   z[k]|=np.array([v&stop for v in tab],dtype=np.uint64)[arg]
   z[k+1]|=np.array([v>>64 for v in tab],dtype=np.uint64)[arg]
 def key(x):return np.ascontiguousarray(x.T).view(np.dtype((np.void,64))).reshape(-1)
 idx=np.argsort(key(sl));w=key(z);p=idx[np.searchsorted(key(sl)[idx],w)]
 assert np.array_equal(z,sl[:,p]);return p
pairs={};Ms={}
for i in S:
 for j in S:
  if i==j:continue
  u,v,g=perm(i,j)
  if (u,v)not in Ms:
   Ms[u,v]=matrix(u,v);print('matrix',u,v,time.time()-t0,flush=True)
  hp=remap(i,u,g);hr=remap(j,v,g);pairs[i,j]=(Ms[u,v],hp,np.argsort(hr))
def firstorbs(sub,i,domain):
 # generate stabilizer of (sub,i) by color-preserving rotations/reflections within each
 # component and swaps between isomorphic marked components
 sig=lambda x:2 if x==i else int(x in sub)
 gens=[]
 for b in starts:
  n=size[b]
  loc=lambda b,t,x:b+((t+((-x+b)if t%2 else x-b))%n)
  for t in range(1,n):
   F=tuple(loc(b,t,x) if block[x]==b else x for x in S)+(12,13)
   if all(sig(x)==sig(F[x])for x in S):gens.append(F)
  for b2 in starts:
   if b2<=b or size[b2]!=n:continue
   hit=None
   for t in range(n):
    zz={x:b2-b+loc(b,t,x) for x in S if block[x]==b}
    if all(sig(x)==sig(y) for x,y in zz.items()):hit=zz;break
   if hit:
    swap=dict(hit);swap.update({y:x for x,y in hit.items()});gens.append(tuple(swap.get(x,x) for x in range(14)))
 assert all(g[i]==i and set(g[j]for j in sub)==set(sub) and sorted(g)==list(range(14)) and all(g[l(j)]==l(g[j]) and g[r(j)]==r(g[j]) for j in S) for g in gens)
 G=[remap(i,i,g) for g in gens];remain=set(map(int,np.flatnonzero(domain)));rep=[]
 while remain:
  y=min(remain);remain.remove(y);rep.append(y);q=[y]
  for v in q:
   for p in G:
    t=int(p[v])
    if t in remain:remain.remove(t);q.append(t)
 return rep
# Compress 220 supports up to color-preserving component moves
gens=[]
for b in starts:
 w=size[b]
 for t in range(1,w):
  gens.append(tuple(b+((t+(-j+b if t%2 else j-b))%w)if block[j]==b else j for j in S))
 for c in starts:
  if c>b and size[c]==w:
   gens.append(tuple(j+c-b if block[j]==b else j+b-c if block[j]==c else j for j in S))
assert all(sorted(g)==list(S) and all(g[l(j)]==l(g[j]) and g[r(j)]==r(g[j]) for j in S) for g in gens)
subsets=[];unseen=set(it.combinations(S,9))
while unseen:
 sub=min(unseen);subsets.append(sub);queue=[sub];unseen.remove(sub)
 for cur in queue:
  for g in gens:
   new=tuple(sorted(g[i] for i in cur))
   if new in unseen:unseen.remove(new);queue.append(new)
assert expected[parts]==len(subsets)
print('subsets',len(subsets),time.time()-t0,flush=True)
def prop(sub,D,queue):
 for j in queue:
  for i in sub:
   if i==j:continue
   ix=np.flatnonzero(D[i]); jy=np.flatnonzero(D[j]); M,p,inv=pairs[i,j];
   if len(jy)*RR[i].shape[1] < 2*len(ix)*RR[j].shape[1]:
    Q,hp,hinv=pairs[j,i]; w=np.bitwise_or.reduce(Q[hp[jy]],axis=0); yy=np.unpackbits(w,bitorder='little')[:len(hinv)];v=np.empty(len(hinv),bool);v[hinv]=yy;yes=v[ix]
   else:
    target=np.packbits(D[j][inv],bitorder='little');yes=np.zeros(len(ix),bool)
    for c in range(0,len(ix),512):
     x=ix[c:c+512];yes[c:c+512]=(M[p[x]]&target).any(axis=1)
   if not yes.any():return False
   if not yes.all():D[i][ix[~yes]]=False;queue.append(i)
 return True
def solve(sub):
 nodes=trials=0
 D={i:np.ones(RR[i].shape[1],bool)for i in sub}
 def go(D):
  nonlocal nodes,trials;nodes+=1
  i=min((j for j in sub if D[j].sum()>1),key=lambda j:D[j].sum(),default=-1)
  if i==-1:return [int(np.flatnonzero(D[j])[0])for j in sub]
  for v in firstorbs(sub,i,D[i]) if nodes==1 else np.flatnonzero(D[i]):
   trials+=1;d={j:D[j].copy()for j in sub};d[i][:]=0;d[i][v]=1
   if prop(sub,d,[i]):
    out=go(d)
    if out:return out
  return None
 if prop(sub,D,list(sub)):
  out=go(D)
 else:out=None
 return nodes,trials,out
for k,sub in enumerate(subsets):
 nodes,trials,out=solve(sub); print('sub',k,sub,'nodes',nodes,'trials',trials,'out',out,'s',time.time()-t0,flush=True)
 assert out is None,(parts,sub,out)
import resource
print('PASS: all nine-index subsets excluded for',parts,'seconds',round(time.time()-t0,1),'maxrss',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
