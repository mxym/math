"""Exact ten-fiber C5 array and good-prism pentagon exclusion, using only NumPy and the standard library.
Run with assertions enabled. See partial-k6-10.md for the proof, counting conventions and shard commands."""
if not __debug__:raise RuntimeError("Do not disable assertions")
from itertools import combinations,permutations,product
import numpy as np
import sys,time
from collections import Counter,defaultdict
import functools,math
P=np.array(list(permutations(range(3))),dtype=np.int8);I=np.array([list(map(tuple,P)).index(tuple(np.argsort(z)))for z in P],dtype=np.int8)
# comp[a,b] maps z -> a[b[z]]
comp=np.array([[list(map(tuple,P)).index(tuple(p[q]))for q in P]for p in P],dtype=np.int8)
def build(m):
 M=[frozenset((i,(i+1)%5))for i in range(m)];E=[frozenset(x)for x in combinations(range(6),2)if frozenset(x)not in M];n=len(E)
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
 assert (n,len(G),len(H),free)==(10,5,20,6) and len({root(i)for i in range(n+len(G))})==1
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
 assert (cores,orbit)==(8606,1567)
 print('m',m,'core survivors',cores,'conjugacy orbits',orbit,'time',time.time()-start,'samples',save[:3],flush=True)
def population_checks(M,E,G,W):
 n=len(E); S=[sum(1<<i for i in w) for w in W];grid=[sum(1<<i for i in t)for t in G]
 assert set(S)=={s for s in range(1<<n) if all((s&g).bit_count()==1 for g in grid)}
 assert all(any(not f&g and len(f|g|e)==6 for f,g in combinations(E,2))for e in M)
 # Connected nonbipartite abstract graph: adjacent degree equations p_a+p_b=18 determine p.
 seen={0}
 for _ in range(6):seen.update(k for f in E if seen&f for k in f)
 assert len(seen)==6 and any(all(frozenset(pair) in E for pair in combinations(t,2))for t in combinations(range(6),3))
 assert all(len(w)>=3 for w in W)  # binary population of each literal contact word

def balanced_anchor(f,star,M,E,W):
 # All possible exterior-class degrees of a core site in f, by two-walk equations to each fiber.
 n=len(E); C=np.array([[2 if a==b else int(not E[a]&E[b])for b in range(n)]for a in range(n)],dtype=int)
 rhs=np.array([16 if f==g else 5 if not E[f]&E[g] else 6 for g in range(n)])-C[f]@C
 U=np.array([[int(g in w)for w in W]for g in range(n)]);T=[]
 for a in range(6):
  b,c=next((b,c)for b,c in combinations(set(range(6))-{a},2)if all(frozenset(t)in E for t in ((a,b),(a,c),(b,c))))
  T.append(tuple(E.index(frozenset(t))for t in ((a,b),(a,c),(b,c))))
 vals=set()
 for v in product(range(4),repeat=len(M)):
  r=rhs-U[:,6:]@v;tw=[r[i]+r[j]-r[k]for i,j,k in T]
  if any(q<0 or q%2 for q in tw):continue
  h=tuple(q//2 for q in tw)+v
  if sum(h)==14-sum(C[f]) and np.array_equal(U@h,rhs) and all(not q or U[f,j] for j,q in enumerate(h)):vals.add(h[star])
 return vals


def canonical(tw,m=5,carry=False):
 M,E,G,H,v,path,tests,pairs=build(m);n=len(E);N=n+len(G);q=len(H)
 parent=list(range(N));tree=[];ch=[]
 def rr(i):
  while i!=parent[i]:i=parent[i]
  return i
 for j,(x,y)in enumerate(H):
  a,b=rr(x),rr(y)
  if a!=b:parent[a]=b;tree.append(j)
  else:ch.append(j)
 base=[0]*q
 for i,x in zip(ch,tw):base[i]=x
 maps={(u,v):(j,0)for j,(u,v)in enumerate(H)};maps.update({(v,u):(j,1)for j,(u,v)in enumerate(H)})
 ret=[]
 for sg in (-1,1):
  for s in range(5):
   ff=[(sg*i+s)%5 for i in range(5)]+[5]
   tE=[E.index(frozenset(ff[i]for i in e))for e in E]
   t=tE+[n+G.index(tuple(sorted(tE[k]for k in t)))for t in G]
   phi=[-1]*q
   for j,(u,v)in enumerate(H):
    k,inv=maps[t[u],t[v]];phi[k]=int(I[base[j]])if inv else base[j]
   assert min(phi)>=0
   p={0:0}
   while len(p)<N:
    old=len(p)
    for k in tree:
     i,j=H[k]
     if i in p and j not in p:p[j]=int(comp[phi[k],p[i]])
     elif j in p and i not in p:p[i]=int(comp[I[phi[k]],p[j]])
    assert len(p)>old
   assert all(comp[I[p[H[k][1]]],comp[phi[k],p[H[k][0]]]]==0 for k in tree)
   z0=[int(comp[I[p[H[k][1]]],comp[phi[k],p[H[k][0]]]])for k in ch]
   cc=min(tuple(int(comp[a,comp[z,I[a]]])for z in z0)for a in range(6))
   ret.append(cc)
 return min(ret),len(set(ret))
def reduced():
 raw=list(twists(5));assert len(set(raw))==1567
 classes=defaultdict(list);claimed={}
 for t in raw:
  rep,size=canonical(t);classes[rep].append(t);claimed[t]=size
 assert len(classes)==185 and all(key==min(xs) and all(claimed[x]==len(xs)for x in xs)for key,xs in classes.items())
 assert Counter(map(len,classes.values()))=={1:3,2:2,5:48,10:132}
 print('D5 classes: 185; multiplicities 3x1, 2x2, 48x5, 132x10',flush=True)
 return sorted(classes)

def study(want):
 m=5
 M,E,G,H,v,path,tests,pairs=build(m);n=len(E);K=3*n
 p=[9]*6+[3]*m
 W=[[i for i,f in enumerate(E)if a in f]for a in range(6)]+[[i for i,f in enumerate(E)if not e&f]for e in M]
 population_checks(M,E,G,W)
 z0=[];keys=[]
 for j,w in enumerate(W):
  for t in product(range(3),repeat=len(w)):
   q=np.zeros(K,dtype=np.int8);q[[3*i+b for i,b in zip(w,t)]]=1;z0.append(q);keys.append(j)
 z0=np.array(z0,dtype=np.int8);keys=np.array(keys);ii,jj=np.triu_indices(K,1);idxi=np.arange(K)
 eye=np.eye(K,dtype=int);cnt=Counter();start=time.time()
 for ig,tw in enumerate(reduced()):
  if not want(ig):continue
  cnt['cases']+=1
  A=np.zeros((K,K),dtype=np.int8);perm=(0,)+tw
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
  if min(counts)==0:cnt['empty']+=1;continue
  # all target pairs with B>0 need coverage
  kk=np.flatnonzero((ii//3!=jj//3)&(B[ii,jj]>0));R=np.vstack([(s==i)for i in range(len(p))]+[Z.T,Z[:,ii[kk]].T*Z[:,jj[kk]].T])
  b=np.r_[p,B.diagonal(),B[ii[kk],jj[kk]]]
  if not R.any(axis=1).all():cnt['uncovered']+=1;continue
  # For each missing edge its sole complementary present prism fixes a bijection at one fiber.
  cats=[]
  for j in range(6,6+m):
   e=M[j-6];r=next((x,y)for x,y in combinations(range(n),2)if not E[x]&E[y] and len(E[x]|E[y]|e)==6)
   cl=np.flatnonzero(s==j);nmat=Z[cl].copy();p1,p2=r;gs=[cl[nmat[:,3*p1+i]>0]for i in range(3)]
   h0=[];wpre=Z[:,ii[kk]]*Z[:,jj[kk]]
   for ids in product(*gs):
    zz=Z[list(ids)]
    if max(zz[0]@zz[1],zz[0]@zz[2],zz[1]@zz[2])>2:continue
    if np.any(wpre[list(ids)].sum(axis=0)>B[ii[kk],jj[kk]]):continue
    # Type e must cover all rung pairs of the prisms complementary to its missing edge.
    if any(len({int(np.argmax(z[3*x:3*x+3]))for z in zz})!=3 for x,y in combinations(range(n),2) if not E[x]&E[y]and len(E[x]|E[y]|e)==6):continue
    h0.append(tuple(sorted(ids)))
   h0=sorted(set(h0));cats.append(h0)
  assert max(map(len,cats))<=729
  # Each ordinary 9-word class is solved for fixed special-word arrangements via a three-slice exact marginal operator.
  Zm=[sum(1<<int(i)for i in np.flatnonzero(z))for z in Z]
  conflict=[sum(1<<k for k,w in enumerate(Zm)if (v&w).bit_count()>=3)for v in Zm]
  allv=lambda ids:sum(1<<int(k)for k in ids)
  sc=[]
  for j in range(6):
   fw=W[j][:];anchor=next((f for f in fw if sum(1 for x,y in combinations(M,2)if not x&y and not (x|y)&E[f])==0),fw[0])
   anchors=balanced_anchor(anchor,j,M,E,W)
   assert anchors and anchors<=({1,2,3,4}if j==5 else {3})
   fw.remove(anchor);fw=[anchor]+fw
   a0=[k for k in range(len(Z))if s[k]==j];full=[(x,y,u,v)for x,y in combinations(fw,2)for u in range(3)for v in range(3)]
   BI=[int(B[3*x+u,3*y+v])for x,y,u,v in full];base=sum(zz<<(5*k)for k,zz in enumerate(BI));Aflag=sum(1<<(5*k)for k in range(len(BI)))
   codes=[sum((1<<(5*l))for l,(x,y,u,v)in enumerate(full)if z[3*x+u]and z[3*y+v])for z in Z]
   anchor_mask=[sum(31<<(5*k)for k,(x,y,a,b)in enumerate(full)if x==anchor and a==t)for t in range(3)]
   nonmask=sum(31<<(5*k)for k,(x,y,a,b)in enumerate(full)if x!=anchor)
   sliced=[];sis=[]
   for t in range(3):
    loc=[k for k in a0 if Z[k,3*anchor+t]];X={}
    for ids in (v for cnt0 in ((1,2,3,4)if j==5 else (3,))for v in combinations(loc,cnt0)):
     if any((Zm[a]&Zm[b]).bit_count()>=3 for a,b in combinations(ids,2)):continue
     sig0=sum(codes[k]for k in ids)
     if ((base+(Aflag*16)-sig0)&(Aflag*16))!=(Aflag*16):continue
     mask0=allv(ids);con=0
     for j0 in ids:con|=conflict[j0]
     X.setdefault(sig0&anchor_mask[t],[]).append((sig0&nonmask,mask0,con))
    sliced.append(X);sis.append(sum(map(len,X.values())))
   impact=[i for i,e in enumerate(M)if len(set(fw)&set(W[6+i]))>=2]
   tab=[]
   for cat in cats:
    tab.append([(sum(codes[k]for k in ids),int(conflict[ids[0]]|conflict[ids[1]]|conflict[ids[2]]))for ids in cat])
   sc.append((base,Aflag,nonmask,anchor_mask,sliced,impact,tab))
  from functools import lru_cache
  @lru_cache(maxsize=50000)
  def table(j,combs):
   base,flag,nmask,ams,sl,impact,tab=sc[j];a=0;ban=0
   for q,i in zip(impact,combs):
    z,c=tab[q][i];a+=z;ban|=c
   target=base-a
   if ((base+16*flag-a)&(16*flag))!=16*flag:return ()
   z=[[(h,x,c)for h,x,c in sl[g].get(target&ams[g],[])if not x&ban]for g in range(3)]
   if any(not zz for zz in z):return ()
   z.sort(key=len);lookup={}
   for k,x,c in z[2]:lookup.setdefault(k,[]).append(x)
   result=[];t2=target&nmask
   for k,x,c in z[0]:
    for h,y,d in z[1]:
     if c&y:continue
     for v in lookup.get(t2-k-h,()):
      if not (c|d)&v:result.append(x|y|v)
   return tuple(result)
  # Quotient an exceptional triple table only for local compatibility: each outer star sees one
  # pair projection of each of two exceptional types. Triple conflicts with them are impossible (only 2 shared fibers).
  req0=b.copy()
  compat={};pc=Counter()
  for i in range(5):
   imp=sc[i][5];assert len(imp)==2 and all(len(set(W[i])&set(w))<=2 for w in W[6:]);a,b=imp;ta=sc[i][6]
   t1=defaultdict(list);t2=defaultdict(list)
   for j,(q,ban)in enumerate(ta[a]): t1[q].append(j)
   for j,(q,ban)in enumerate(ta[b]): t2[q].append(j)
   adj=[set()for _ in cats[a]];num=0
   for lv in t1.values():
    for rv in t2.values():
     if table(i,(lv[0],rv[0])):
      num+=len(lv)*len(rv)
      for j in lv:adj[j].update(rv)
   compat[a,b]=adj;rev=[set()for _ in cats[b]]
   for j,nei in enumerate(adj):
    for v0 in nei:rev[v0].add(j)
   compat[b,a]=rev
   # pair census
  cyc=[0]
  while len(cyc)<5:cyc.append(min(b for a,b in compat if a==cyc[-1] and b not in cyc))
  w=[]
  for j in range(5):
   a,b=cyc[j],cyc[(j+1)%5]
   w.append(np.array([[int(bv in rr)for bv in range(len(cats[b]))]for rr in compat[a,b]],dtype='int64'))
  # No fixed-width overflow: each of five catalog domains has size <=729.
  assert 729**5 < 2**63
  ar=w[0]
  for wa in w[1:]:ar=ar@wa
  paths=int(ar.trace());cnt['outer cycles']+=paths
  if not paths:cnt['empty cycle']+=1;continue
  if paths>6000000:print('working',ig,'outer cycles',paths,flush=True)
  ct=Counter();seenbits=set();cix=[0]*5
  j=5;base,flag,nmask,ams,sl,impact,tab=sc[j];high=16*flag;coded=base+high
  cproj=[[v[0]for v in tt]for tt in tab];banp=[[v[1]for v in tt]for tt in tab]
  @lru_cache(maxsize=30000)
  def joined(s0,s1,s2,tar,ban):
   data=[[(h,x,c)for h,x,c in sl[g].get(sig0,())if not x&ban]for g,sig0 in enumerate((s0,s1,s2))]
   if any(not group for group in data):return ()
   data.sort(key=len);last=defaultdict(list)
   for h,x,_ in data[2]:last[h].append(x)
   res=[]
   for h,x,c in data[0]:
    for d,y,t in data[1]:
     if c&y:continue
     for z in last.get(tar-h-d,()):
      if not (c|t)&z:res.append(x|y|z)
   return tuple(res)
  # Exact graph row: collision of two previously selected exterior neighbors sharing 2 core sites is forbidden.
  # At a saturated root with no unmet equality further ensure zero-core-cap edges can be paired into exterior triangles.
  masks=[int(z)for z in Zm]
  deg0=2-Z-Z@A
  conf2=[sum(1<<j for j,bb in enumerate(masks)if (rr&bb).bit_count()>=2)for rr in masks]
  eligible=[]
  for i,wi in enumerate(masks):
   elig=0
   for j,wj in enumerate(masks):
    z=wi&wj
    if i==j or z.bit_count()>=2:continue
    if z:
     xx=z.bit_length()-1
     if not deg0[i,xx] or not deg0[j,xx]:continue
    elig|=1<<j
   eligible.append(elig)
  def indices(x):
   while x:z=x&-x;x-=z;yield z.bit_length()-1
  allpts=((1<<len(Z))-1,)+tuple(sum(1<<j for j,w in enumerate(masks)if w>>i&1)for i in range(K))
  @lru_cache(maxsize=300000)
  def onerow(ri,avail):
   w=masks[ri];dem=(14-w.bit_count(),)+tuple(map(int,deg0[ri]));blue=sum(1<<j for j in indices(avail)if not masks[j]&w)
   def match(pool):
    if not pool:return True
    k=(pool&-pool).bit_length()-1;nxt=pool^(1<<k)
    for t in indices(nxt&eligible[k]):
     if not masks[k]&masks[t] and match(nxt^(1<<t)):return True
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
  rowfails=Counter()
  # D5 reverse orientation need never be assumed a symmetry of a particular code; counts below are labelled.
  def reciprocal(inds):
   import functools,math
   ww=[sum(1<<int(k)for k in np.flatnonzero(Z[j]))for j in inds]
   assert len(set(ww))==69
   req=np.array([int(i in inds)for i in range(len(Z))]);assert np.array_equal(R@req,req0)
   def bits(r):
    while r:q=r&-r;r-=q;yield q.bit_length()-1
   nm=np.array(2-Z[inds]-Z[inds]@A,dtype=int);valid=[]
   for i,w in enumerate(ww):
    ids=[j for j,v in enumerate(ww)if i!=j and (v&w).bit_count()<=1 and not any(not nm[i,k]or not nm[j,k]for k in bits(v&w))]
    valid.append(sum(1<<j for j in ids))
   c2=[sum(1<<j for j,v in enumerate(ww)if (v&w).bit_count()>=2)for w in ww];cv=[(1<<69)-1]+[sum(1<<j for j,w in enumerate(ww)if w>>i&1)for i in range(K)]
   @functools.lru_cache(maxsize=30000)
   def bm(pool):
    if not pool:return True
    k=(pool&-pool).bit_length()-1;rem=pool^(1<<k)
    return any(not ww[k]&ww[t] and bm(rem^(1<<t))for t in bits(rem&valid[k]))
   def rows(i):
    w=ww[i];dem=(14-w.bit_count(),)+tuple(map(int,nm[i]));blue=sum(1<<j for j,v in enumerate(ww)if not w&v);res=[]
    def dfs(pool,b,sel):
     if b[0]==0:
      if not any(b[1:]) and bm(sel&blue):res.append(sel)
      return
     yes=no=0;best=None
     for col,nv in enumerate(b):
      mm=pool&cv[col];nn=mm.bit_count()
      if nv<0 or nv>nn:return
      if nv==0:no|=mm
      elif nv==nn:yes|=mm
      elif col:
       key=math.comb(nn,nv)
       if best is None or key<best[0]:best=(key,mm)
     if not(yes or no):
      k=best[1]if best else pool;ii0=k&-k
      dfs(pool^ii0,b,sel);yes=ii0
     if yes&no:return
     dont=0
     for k in bits(yes):
      if yes&c2[k]&~(1<<k):return
      dont|=c2[k]
     dfs(pool&~(no|dont|yes),tuple(nv-(yes&col).bit_count()for nv,col in zip(b,cv)),sel|yes)
    dfs(valid[i],dem,0);return res
   rowsall=[rows(i)for i in range(69)]
   lens=list(map(len,rowsall));assert min(lens)>0
   caps=[[2-(x&y).bit_count()for y in ww]for x in ww]
   @functools.lru_cache(maxsize=200000)
   def compE(i,h,j):
    row=rowsall[i][h];edge=(row>>j)&1;quota=caps[i][j]-edge
    return sum(1<<k for k,v in enumerate(rowsall[j])
               if ((v>>i)&1)==edge and (v&row).bit_count()==quota)
   no=[0]
   def rec(dom,path):
    no[0]+=1
    if not dom:return path
    i=min(dom,key=lambda j:dom[j].bit_count())
    for h in bits(dom[i]):
     hd={}
     for j,v in dom.items():
      if i==j:continue
      x=v&compE(i,h,j)
      if not x:break
      hd[j]=x
     else:
      out=rec(hd,path+[(i,h)])
      if out is not False:return out
    return False
   out=rec({i:(1<<l)-1 for i,l in enumerate(lens)},[])
   if out is not False:
    adj=[set(np.flatnonzero(a).tolist())for a in A]
    adj+= [set()for _ in range(69)]
    for v,h in out:
     av=ww[v];row=rowsall[v][h]
     for k in bits(av):adj[k].add(K+v);adj[K+v].add(k)
     for k in bits(row):adj[K+v].add(K+k)
    assert len(adj)==99 and all(len(q)==14 and i not in q for i,q in enumerate(adj))
    assert all((i in adj[j])==(j in adj[i])and len(adj[i]&adj[j])==2-int(j in adj[i])for i,j in combinations(range(99),2))
    print('ACTUAL VERIFIED SRG',list(map(sorted,adj)),flush=True)
    raise RuntimeError('actual graph found')
   return no[0],min(lens),max(lens)

  def walk(level,csum,ban):
   k=cyc[level];prev=cyc[level-1]
   cand=range(len(cats[k]))if not level else compat[prev,k][cix[prev]]
   if level==4:cand=cand & compat[0,k][cix[0]]
   for v in cand:
    cix[k]=v;zz=csum+cproj[k][v]
    if (coded-zz)&high!=high:continue
    if level<4:
     walk(level+1,zz,ban|banp[k][v]);continue
    ct['cap']+=1;t=base-zz;sgs=(t&ams[0],t&ams[1],t&ams[2])
    if any(aa not in lut for aa,lut in zip(sgs,sl)):continue
    ct['anchor']+=1
    cc=joined(*sgs,t&nmask,ban|banp[k][v])
    if not cc:continue
    ct['cap+center']+=1;ct['centers']+=len(cc)
    opts=[table(j,tuple(cix[q]for q in sc[j][5]))for j in range(5)]
    import math
    mult=math.prod(map(len,opts));ct['codes']+=mult*len(cc)
    # Every valid ordinary layer combination is retested against the literal core diagonals/pairs.
    spbits=allv(j for v,c in enumerate(cix)for j in cats[v][c])
    for os in product(*opts,cc):
     bits=spbits
     for bb in os:bits|=bb
     inds=list(indices(bits))
     assert len(inds)==69 and bits not in seenbits;seenbits.add(bits)
     zz=np.zeros(len(Z),dtype=int);zz[inds]=1
     if not np.array_equal(R@zz,req0):ct['diagonal_reject']+=1;continue
     # Noncentral ordinary fibers share at most one label, special-special at most two;
     # central/exceptions have already been filtered. Direct global cross-check.
     if any((conflict[i]&bits)!=(1<<i)for i in inds):ct['trip_reject']+=1;continue
     for i in sorted(inds,key=lambda j:((eligible[j]&bits).bit_count(),-len(W[s[j]]))):
      if not onerow(i,bits&eligible[i]):rowfails[int(s[i])]+=1;ct['veto']+=1;break
     else:
      ct['all_integer_rows']+=1
      nodes,lo,hi=reciprocal(inds);ct['reciprocity_nodes']+=nodes;ct['reciprocity_veto']+=1
      print('terminal',ig,ct['all_integer_rows'],'nodes',nodes,'domain',lo,hi,flush=True)
  walk(0,0,0)
  assert ct['codes']==ct['diagonal_reject']+ct['trip_reject']+ct['veto']+ct['reciprocity_veto']
  cnt['merged']+=ct['codes'];cnt['invalid merges']+=ct['diagonal_reject']+ct['trip_reject']
  cnt['row vetoes']+=ct['veto'];cnt['terminal']+=ct['reciprocity_veto'];cnt['terminal nodes']+=ct['reciprocity_nodes']
  if ct['codes']:print('contact codes',ig,tw,ct['codes'],'row vetoes',ct['veto'],'terminal vetoes',ct['reciprocity_veto'],flush=True)
 assert cnt['cases']==sum(want(i)for i in range(185))
 print('TOTAL',dict(cnt),'seconds',round(time.time()-start,3),flush=True)
 if cnt['cases']==185:
  assert cnt['outer cycles']==175776281 and cnt['merged']==27861 and not cnt['invalid merges']
  assert cnt['row vetoes']==27851 and cnt['terminal']==10
if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser(description=__doc__)
 a.add_argument('--shards',type=int,default=1);a.add_argument('--shard',type=int,default=0)
 a.add_argument('--case',type=int,help='Optional single zero-based D5 case, 0..184.')
 r=a.parse_args();assert 0<=r.shard<r.shards and (r.case is None or 0<=r.case<185)
 study(lambda i:i%r.shards==r.shard and (r.case is None or i==r.case))
