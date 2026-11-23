"""No two good and one further equal-prism partner at an anticomplete pair in SRG(99,14,1,2). Python 3.10+ and NumPy only.
Run with assertions enabled. No graph-symmetry assumption or solver is used."""
if not __debug__:raise RuntimeError('do not disable assertions')
from itertools import combinations,permutations,product
import numpy as np
import sys,time
from collections import Counter,defaultdict
P=np.array(list(permutations(range(3))),dtype=np.int8);I=np.array([list(map(tuple,P)).index(tuple(np.argsort(z)))for z in P],dtype=np.int8)
# comp[a,b] maps z -> a[b[z]]
comp=np.array([[list(map(tuple,P)).index(tuple(p[q]))for q in P]for p in P],dtype=np.int8)
def build(m):
 M=list(map(frozenset,[(0,1),(2,3),(2,4),(2,5),(3,4)]));E=[frozenset(x)for x in combinations(range(6),2)if frozenset(x)not in M];n=len(E)
 G=[t for t in combinations(range(n),3)if len(set().union(*[E[i]for i in t]))==6];owner={tuple(sorted(q)):n+j for j,t in enumerate(G)for q in combinations(t,2)}
 H=[(i,n+j)for j,t in enumerate(G)for i in t]+[(i,j)for i,j in combinations(range(n),2)if not E[i]&E[j]and(i,j)not in owner]
 pa=list(range(n+len(G)));D={};free=0
 def root(i):
  while pa[i]!=i:i=pa[i]
  return i
 for i,j in H:
  ri,rj=root(i),root(j)
  if ri!=rj:pa[ri]=rj;D[i,j]=0;D[j,i]=0
  else:free+=1;D[i,j]=free;D[j,i]=-free
 assert len({root(i) for i in range(n+len(G))})==1
 assert (n,len(G),len(H),free)==(10,4,20,7)
 def path(i,j):
  def fg(i,j):
   q=tuple(sorted((i,j)))
   if q in owner:return (D[i,owner[q]],D[owner[q],j])
   return (D[i,j],)
  return tuple(v for v in fg(i,j)if v)
 pair=[(i,j,[k for k in range(n)if not(E[i]|E[j])&E[k]]) for i,j in combinations(range(n),2)if E[i]&E[j]]
 # batch evaluate composites from actual f-sites to g-sites.
 tests=[[(path(i,k)+path(k,j))for k in K]for i,j,K in pair if len(K)>=3]
 return M,E,G,H,free,path,tests,pair
def twists(m):
 M,E,G,H,v,path,tests,pairs=build(m);print('free',v,'core guards',len(tests),flush=True);cores=0;orbit=0;start=time.time();save=[]
 # fix up to simultaneous conjugacy (prefix chosen lex).
 conj=np.array([[comp[t,comp[p,I[t]]]for p in range(6)]for t in range(6)])
 tail=np.array(list(product(range(6),repeat=v-3)),dtype=np.int8).T
 sz=tail.shape[1]
 for pre in product(range(6),repeat=3):
  pis=sorted(set(tuple(t[list(pre)])for t in conj));
  if tuple(pre)!=pis[0]:continue
  mat=np.vstack([np.zeros(sz,dtype=np.int8),np.repeat(np.array(pre,dtype=np.int8)[:,None],sz,axis=1),tail]);cache={():mat[0]}
  def st(w):
   if w not in cache:
    zz=mat[abs(w[-1])]
    cache[w]=comp[zz if w[-1]>0 else I[zz],st(w[:-1])]
   return cache[w]
  ok=np.ones(sz,dtype=bool)
  for terms in tests:
   a,b,c=[st(w)for w in terms]
   for g in range(3):ok &= ~((P[a,g]==P[b,g])&(P[a,g]==P[c,g]))
  ids=np.flatnonzero(ok);cores+=len(ids)*len(pis)
  if len(ids) and len(save)<10:
   save.extend(tuple(map(int,z))for z in mat[1:,ids[:10]].T)
  if len(ids):
   for t in conj:
    if tuple(t[list(pre)])!=tuple(pre):continue
    A=t[tail];cond=np.ones(sz,dtype=bool);eq=cond.copy()
    for tt,rr in zip(tail,A):
     cond &= ~(eq&(tt>rr));eq &= tt==rr
    ok &= cond
   orbit+=np.count_nonzero(ok)
   for z in mat[1:,np.flatnonzero(ok)].T:
    yield tuple(map(int,z))
 
 pass
 assert (cores,orbit)==(76336,13178)
 print('m',m,'core survivors',cores,'conjugacy orbits',orbit,'time',time.time()-start,'samples',save[:3],flush=True)

def reduced():
 raw=list(twists(5));R=np.array(raw,dtype=np.int8);nj=len(R)
 M,E,G,H,v,path,tests,pairs=build(5);n=len(E);N=n+len(G);q=len(H)
 parent=list(range(N));tree=[];ch=[]
 def rr(i):
  while i!=parent[i]:i=parent[i]
  return i
 for j,(x,y)in enumerate(H):
  a,b=rr(x),rr(y)
  if a!=b:parent[a]=b;tree.append(j)
  else:ch.append(j)
 base=np.zeros((q,nj),dtype=np.int8);base[ch]=R.T; maps={(u,v):(j,0)for j,(u,v)in enumerate(H)};maps.update({(v,u):(j,1)for j,(u,v)in enumerate(H)})
 weights=np.array([6**i for i in reversed(range(v))],dtype=np.int64)
 code=weights@R.T;mins=code.copy(); orbit=[]
 for a,b in [(0,1),(1,0)]:
  for h in [(3,4,5),(4,3,5)]:
   ff=(a,b,2)+h;tE=[E.index(frozenset(ff[i]for i in e))for e in E]
   t=tE+[n+G.index(tuple(sorted(tE[k]for k in g)))for g in G];phi=np.zeros_like(base)
   for j,(u,vv)in enumerate(H):
    k,iv=maps[t[u],t[vv]];phi[k]=I[base[j]] if iv else base[j]
   p={0:np.zeros(nj,dtype=np.int8)}
   while len(p)<N:
    old=len(p)
    for k in tree:
     i,j=H[k]
     if i in p and j not in p:p[j]=comp[phi[k],p[i]]
     elif j in p and i not in p:p[i]=comp[I[phi[k]],p[j]]
    assert len(p)>old
   assert all(np.all(comp[I[p[H[k][1]]],comp[phi[k],p[H[k][0]]]]==0)for k in tree)
   z=np.array([comp[I[p[H[k][1]]],comp[phi[k],p[H[k][0]]]]for k in ch])
   zz=np.minimum.reduce([weights@comp[t,comp[z,I[t]]]for t in range(6)]);mins=np.minimum(mins,zz);orbit.append(zz)
 buckets=defaultdict(set)
 for c,g in zip(mins,code):buckets[c].add(g)
 assert all(c==min(z)for c,z in buckets.items())
 for k,orb in enumerate(np.array(orbit).T):assert set(orb)==buckets[mins[k]]
 keep=R[code==mins].tolist()
 assert len(raw)==13178 and len(keep)==3527 and Counter(map(len,buckets.values()))=={4:3085,2:396,1:46}
 print('new distinct orbits',len(keep),Counter(map(len,buckets.values())),flush=True)
 return keep
def study():
 m=5
 M,E,G,H,v,path,tests,pairs=build(m);n=len(E);K=3*n
 p=[9]*6+[3]*m
 W=[[i for i,f in enumerate(E)if a in f]for a in range(6)]+[[i for i,f in enumerate(E)if not e&f]for e in M]
 S={sum(1<<i for i in w)for w in W};grid=[sum(1<<i for i in g)for g in G]
 # Equal-prism contact vectors for the three partner pairs: each outside site must
 # have identical numbers of contacts in each side of each equality.
 f=lambda a,b:E.index(frozenset((a,b)))
 EQ=[(f(0,2),f(1,i),f(1,2),f(0,i))for i in (3,4,5)]
 def support_ok(s):
  a=lambda i:int(s>>i&1)
  if any((s&g).bit_count()!=1 for g in grid) or any(a(i)+a(j)!=a(k)+a(l)for i,j,k,l in EQ):return False
  F=[i for i in range(n)if a(i)]
  return all(sum(not E[i]&E[j]for j in F)<=1 for i in F)
 assert S=={s for s in range(1<<n)if support_ok(s)}
 # Independent per-support population calculation: aggregate all core pair equations.
 U=np.array([[int(i in w)for w in W]for i in range(n)],dtype=int)
 C=np.array([[2 if i==j else int(not E[i]&E[j])for j in range(n)]for i in range(n)])
 Q=np.array([U[i]*U[j]for i in range(n)for j in range(i,n)],dtype=int)
 B0=3*(12*np.eye(n,dtype=int)+6-C-C@C); assert np.array_equal(Q@p,B0[np.triu_indices(n)])
 # Full rank mod 101 certifies full rational column rank.
 D=Q.copy()%101
 for c in range(len(p)):
  i=next(i for i in range(c,len(D))if D[i,c])
  D[[c,i]]=D[[i,c]];D[c]=D[c]*pow(int(D[c,c]),-1,101)%101
  for j in range(c+1,len(D)):D[j]=(D[j]-D[j,c]*D[c])%101
 assert (np.diag(D[:len(p)])==1).all()

 z0=[];keys=[]
 for j,w in enumerate(W):
  for t in product(range(3),repeat=len(w)):
   q=np.zeros(K,dtype=np.int8);q[[3*i+b for i,b in zip(w,t)]]=1;z0.append(q);keys.append(j)
 z0=np.array(z0,dtype=np.int8);keys=np.array(keys);ii,jj=np.triu_indices(K,1);idxi=np.arange(K)
 eye=np.eye(K,dtype=int);cnt=Counter();census={};start=time.time()
 for ig,tw in enumerate(reduced()):
  if ig%500==0:print('orbits',ig,flush=True)
  A=np.zeros((K,K),dtype=np.int8);perm=(0,)+tuple(tw)
  for i in range(n):A[3*i:3*i+3,3*i:3*i+3]=1-np.eye(3,dtype=np.int8)
  for i,j in combinations(range(n),2):
   if E[i]&E[j]:continue
   z=0
   for a in path(i,j):
    vv=perm[abs(a)];z=comp[vv if a>0 else I[vv],z]
   cc=3*i+np.arange(3);rr=3*j+P[z];A[cc,rr]=A[rr,cc]=1
  # residual outer common-neighbor capacity at each core pair
  B=12*eye+2-A-A@A
  assert B.min()>=0
  # sparse: zero entries ban cooccurrence. Actual one-outside-vertex/core-site common neighbor bound.
  bads=np.where((ii//3!=jj//3)&(B[ii,jj]==0))[0];valid=np.all(z0@A+z0<=2,axis=1)
  for k in bads:valid &= ~(z0[:,ii[k]]&z0[:,jj[k]]).astype(bool)
  Z=z0[valid];s=keys[valid];counts=np.bincount(s,minlength=len(p))
  # A two-entry word can repeat up to its core-pair residual; every longer word is binary.
  X=np.flatnonzero(Z.sum(axis=1)==2);ix=np.repeat(X,[int(B[tuple(np.flatnonzero(Z[i]))])-1 for i in X]);Z=np.vstack([Z,Z[ix]]);s=np.r_[s,s[ix]]
  if min(counts)==0:cnt['empty']+=1;continue
  # all target pairs with B>0 need coverage
  kk=np.flatnonzero((ii//3!=jj//3)&(B[ii,jj]>0));R=np.vstack([(s==i)for i in range(len(p))]+[Z.T,Z[:,ii[kk]].T*Z[:,jj[kk]].T])
  b=np.r_[p,B.diagonal(),B[ii[kk],jj[kk]]]
  if not R.any(axis=1).all():cnt['uncovered']+=1;continue
  Q3={}
  for iz,zw in enumerate(Z):
   for f in combinations(np.flatnonzero(zw),3):Q3.setdefault(f,[]).append(iz)
  qlist=[v for v in Q3.values()if len(v)>=2]
  from functools import lru_cache
  Zm=[sum(1<<int(i)for i in np.flatnonzero(z))for z in Z]
  wmasks=[int(z)for z in Zm]
  deg0=2-Z-Z@A
  conf2=[sum(1<<j for j,bb in enumerate(wmasks)if (rr&bb).bit_count()>=2)for rr in wmasks]
  eligible=[]
  for i,wi in enumerate(wmasks):
   elig=0
   for j,wj in enumerate(wmasks):
    z=wi&wj
    if i==j or z.bit_count()>=2:continue
    if z:
     xx=z.bit_length()-1
     if not deg0[i,xx] or not deg0[j,xx]:continue
    elig|=1<<j
   eligible.append(elig)
  def indices(x):
   while x:z=x&-x;x-=z;yield z.bit_length()-1
  allpts=((1<<len(Z))-1,)+tuple(sum(1<<j for j,w in enumerate(wmasks)if w>>i&1)for i in range(K))
  @lru_cache(maxsize=300000)
  def onerow(ri,avail):
   w=wmasks[ri];dem=(14-w.bit_count(),)+tuple(map(int,deg0[ri]));blue=sum(1<<j for j in indices(avail)if not wmasks[j]&w)
   def match(pool):
    if not pool:return True
    k=(pool&-pool).bit_length()-1;nxt=pool^(1<<k)
    for t in indices(nxt&eligible[k]):
     if not wmasks[k]&wmasks[t] and match(nxt^(1<<t)):return True
    return False
   def solve(pool,b,sel):
    if b[0]==0:return not any(b[1:]) and match(sel&blue)
    yes=no=0;best=None
    for col,nv in enumerate(b):
     mm=pool&allpts[col];cnt=mm.bit_count()
     if nv<0 or nv>cnt:return False
     if nv==0:no|=mm
     elif nv==cnt:yes|=mm
     elif col:
      key=(min(nv,cnt-nv),cnt)
      if best is None or key<best[0]:best=key,mm
    if not (yes or no):
     br=best[1]if best else pool;ii0=br&-br
     if solve(pool^ii0,b,sel):return True
     yes=ii0
    if yes&no:return False
    dont=0
    for k in indices(yes):
     if (conf2[k]&yes)&~(1<<k):return False
     dont|=conf2[k]
    return solve(pool&~(no|dont|yes),tuple(v-(yes&col).bit_count()for v,col in zip(b,allpts)),sel|yes)
   return solve(avail,dem,0)
  leaves=0;failed=Counter();tt=time.time()
  def full(yes):
   nonlocal leaves
   leaves+=1
   # Probe a marked word whose row has already disproved nearby completions first.
   inds=list(indices(yes))
   assert len(inds)==69 and np.array_equal(R[:,inds].sum(axis=1),b)
   inds.sort(key=lambda i:(-failed[i],(eligible[i]&yes).bit_count()))
   for i in inds:
    if not onerow(i,yes&eligible[i]):failed[i]+=1;return False
   print('outrow-pass',ig,leaves,inds,flush=True);return True
  masks=[sum(1<<int(i) for i in np.flatnonzero(r))for r in R]
  qmask=[sum(1<<int(i) for i in v)for v in qlist]
  # Full exact positive equality branching, with forced sums and triple upper capacities.
  from math import comb
  nodes=[0]
  def rec(yes,no):
   nodes[0]+=1
   while True:
    best=None;fo=fc=0
    for mask,bb in zip(masks,b):
     rem=mask&~(yes|no);avail=rem.bit_count();need=int(bb)-(mask&yes).bit_count()
     if need<0 or need>avail:return False
     if not avail:continue
     if not need:fo|=rem
     elif need==avail:fc|=rem
     else:
      score=comb(avail,need)
      if best is None or score<best[0]:best=(score,rem,need,avail)
    for mask in qmask:
     z=mask&yes
     if z:
      if z&(z-1):return False
      fo|=mask&~(yes|no)
    if fo&fc:return False
    if (fo|fc)==0:break
    yes|=fc;no|=fo
   if best is None:return full(yes)
   score,avail,need,k=best;L=[];xx=avail
   while xx:
    lo=xx&-xx;L.append(lo);xx-=lo
   if need>k-need:
    return any(rec(yes|(avail^v),no|v)for inds in combinations(L,k-need)for v in [sum(inds)])
   return any(rec(yes|v,no|(avail^v))for inds in combinations(L,need)for v in [sum(inds)])
  ou=rec(0,0);assert not ou,('unexpected exterior rows',ig)
  if leaves:
   print('contact tables',ig,leaves,flush=True);census[ig]=leaves
  cnt['leaves']+=leaves
  cnt['nodes']+=nodes[0];cnt['reject']+=1
 assert census=={2290:64,2899:16,3099:212,3151:16,3364:3,3496:36,3519:4}
 assert dict(cnt)=={'empty':10,'uncovered':349,'reject':3168,'leaves':351,'nodes':39466}
 print('Final',dict(cnt))

if __name__=='__main__':study()
