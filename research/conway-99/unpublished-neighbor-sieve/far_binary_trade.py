"""A nonzero fixed far-chart trade has binary rank >=6. Python + NumPy, integers only."""
import itertools as it,numpy as np
from collections import Counter
P=list(it.combinations(range(6),2));ix={e:i for i,e in enumerate(P)}
perm=[[ix[tuple(sorted((p[a],p[b])))] for a,b in P] for p in it.permutations(range(6))]
maskmap=lambda k,p:sum(1<<p[t] for t in range(15) if k>>t&1)
O=np.array([[len(set(e)&set(f))==1 for f in P] for e in P],dtype=int)
seen=set();ct=Counter();bydim=Counter();examples=[]
for U in range(1,1<<15):
 if U in seen:continue
 hashes=[maskmap(U,p) for p in perm];seen.update(hashes);auto=[p for p,x in zip(perm,hashes) if x==U]
 I=np.flatnonzero((U>>np.arange(15))&1);m=len(I);Q=O[np.ix_(I,I)];old=set();base=sum(1<<int(i) for i in I)
 # only spanning binary signatures selected, Gram rank must equal four
 X=Q.copy();k=0
 for j in range(m):
  i=next((i for i in range(k,m) if X[i,j]),None)
  if i is None:continue
  X[[k,i]]=X[[i,k]]
  for i in range(k+1,m):
   if X[i,j]:X[i]^=X[k]
  k+=1
 if k!=4:continue
 for sub in range(1<<m):
  dupl=sum((sub>>j&1)<<int(i) for j,i in enumerate(I))
  if dupl in old:continue
  n=1+((dupl>>I)&1);deg=Q@n
  if min(deg)<6 or max(deg)>16 or any(deg%2):continue
  old.update(maskmap(dupl,p) for p in auto)
  ct['degree']+=1
  C=(Q*n)@Q; bound=8-2*Q
  if np.any(np.triu((C>bound)&((n[:,None]==2)|(n[None,:]==2)),1)):continue
  ct['avg']+=1;bydim[m]+=1;examples.append((U,dupl))
assert ct=={'degree':1294,'avg':720}
print('Multiplicity types:',ct,flush=True)

from collections import Counter
stats_leaf=Counter()
from itertools import product
bc=int.bit_count
def bits(xs):return sum(1<<int(k) for k in xs)
def trial(UD):
 U,D=UD;cells=[e for i,e in enumerate(P) if U>>i&1];m=len(cells);mult=[1+((D>>ix[e])&1) for e in cells];rep=list(range(m));neg={i:m+sum(n==2 for n in mult[:i]) for i,n in enumerate(mult) if n==2};rev=rep+list(neg);opp={v:k for k,v in neg.items()};n=len(rev)
 mask=[bits(j for j,b in enumerate(rev) if len(set(e)&set(cells[b]))==1) for e in cells]
 # Reorder each pair of physically antipodal unsigned duplicate rows without cost.
 forest=[];reached=set(i for i in range(m) if i not in neg);unseen=set(neg)
 while unseen:
  nxt=next(((i,j) for i in sorted(unseen) for j in sorted(reached) if mask[i]>>j&1),None)
  if nxt is None: k=min(unseen)
  else:
   k,j=nxt;forest.append((k,j))
  unseen.remove(k);reached.add(k)
 dom=[]
 for a,U0 in enumerate(mask):
  k=bc(U0)//2;opts=[]
  adj=[b for b in range(m) if U0>>b&1]
  du=[b for b in adj if b in neg];su=[b for b in adj if b not in neg]
  for shorts in it.combinations(su,len(su)//2):
   for choices in product(*[(b,neg[b]) for b in du]):
    S=bits(shorts+choices);Z=U0^S
    # necessary unsigned mixed-pair debt, + <=weighted possible cap.
    if sum(bc(mask[rev[s]]&Z) for s in range(n) if S>>s&1)>2*k*k-6*k:continue
    if any((a==i and not(S>>j&1)) or (a==j and not(S>>i&1)) for i,j in forest):continue
    opts.append(S)
  if not opts:return 'domain',0,0
  dom.append(opts)
 # dot sign compatibility; get exact C(p,n) for later.
 LUT=np.array([j.bit_count() for j in range(1<<16)],dtype=np.int16)
 def pop(X):return LUT[X&65535]+LUT[X>>16]
 def pack(z):
  return [int.from_bytes(x.tobytes(),'little') for x in np.packbits(z,axis=1,bitorder='little')]
 comps={};dom0=[(1<<len(x))-1 for x in dom]
 for a in range(m):
  for b in range(a):
   A=np.array(dom[a],np.int64)[:,None];B=np.array(dom[b],np.int64)[None,:];ok=((A>>b)&1)==((B>>a)&1)
   for u in range(mult[a]):
    for v in range(mult[b]):
     p1=A^(mask[a] if u else 0);p2=B^(mask[b] if v else 0);k=(neg[b] if v else b)
     e=(p1>>k)&1;f=((mask[a]>>k)&1)-e
     cap=2-np.maximum(pop(p1&p2)+e,pop((mask[a]^p1)&(mask[b]^p2))+f)
     ok &= (cap>=0)
   if not np.any(ok):return 'pair',0,0
   comps[a,b]=pack(ok);comps[b,a]=pack(ok.T)
 def arc(d):
  changed=True
  while changed:
   changed=False
   for a in range(m):
    for b in range(m):
     if a==b:continue
     da=d[a];rest=0
     while da:
      x=da&-da;da-=x
      if not (comps[a,b][x.bit_length()-1]&d[b]):rest|=x
     if rest:
      d[a]^=rest;changed=True
      if not d[a]:return False
  return True
 if not arc(dom0):return 'arc',0,0
 count=0;ang=0
 def walk(d,assigned):
  nonlocal count,ang
  # Exhaustive: no search limit.
  count+=1
  if len(assigned)==m:
   ang+=1;S=[dom[i][q.bit_length()-1] for i,q in enumerate(d)]
   ss=S+[mask[a]^S[a] for a in neg];allM=mask+[mask[a] for a in neg]
   lo=[allM[i]^s for i,s in enumerate(ss)]
   # true near quota for each signed row per earlier atlas.
   for i in range(n):
    debt=0;k=bc(ss[i])
    for p in range(n):
     if not (ss[i]>>p&1):continue
     for q in range(n):
      if not (lo[i]>>q&1):continue
      debt+=max(bc(ss[p]&ss[q])+(ss[p]>>q&1),bc(lo[p]&lo[q])+(lo[p]>>q&1))
    if debt>2*k*k-6*k:return 0
   F=np.array([[(ss[i]>>j&1)-(lo[i]>>j&1) for j in range(n)] for i in range(n)],dtype=np.int64)
   stats_leaf['word']+=1
   if np.trace(F@F@F)!=0:return 0
   stats_leaf['cubic']+=1
   p=(F>0).astype(int);q=(F<0).astype(int);target=-F-p@p+q@q
   ck=[]
   for i,j in it.combinations(range(n),2):
    if F[i,j]:continue
    K=np.zeros_like(F);K[i,j]=K[j,i]=1
    if all(np.triu(g@g+g,1).max()<=2 for g in (p+K,q+K)):ck.append((i,j))
   def span_test(prime):
    vec=[];ti=np.triu_indices(n)
    for i,j in ck:
     X=np.zeros_like(F);X[i]=F[j];X[j]=F[i];vec.append((X+X.T)[ti])
    # necessary integer solution on common edges
    r=target[ti].copy()%prime
    bas={}
    for v in vec:
     y=v.copy()%prime
     while np.any(y):
      j=np.flatnonzero(y)[0]
      if j not in bas:
       bas[j]=y*pow(int(y[j]),-1,prime)%prime;break
      y=(y-y[j]*bas[j])%prime
    while np.any(r):
     j=np.flatnonzero(r)[0]
     if j not in bas:return False
     r=(r-r[j]*bas[j])%prime
    return True
   if not span_test(2):
    stats_leaf['K2']+=1;return 0
   return 1
  a=min((i for i in range(m) if i not in assigned),key=lambda i:d[i].bit_count())
  cand=d[a]
  while cand:
   x=cand&-cand;cand-=x;j=x.bit_length()-1;e=d.copy();e[a]=x;ok=True
   for b in range(m):
    if a==b:continue
    e[b]&=comps[a,b][j]
    if not e[b]:ok=False;break
   if ok:
    ans=walk(e,assigned|{a})
    if ans:return ans
  return 0
 ans=walk(dom0,set());return ('sign' if ans else 'none'),count,ang
stats=Counter();nodes=0;largest=0;leaves=0
for h in examples:
 st,c,k=trial(h);stats[st]+=1;nodes+=c;leaves+=k;largest=max(largest,c)
assert stats=={'domain':578,'pair':96,'arc':26,'none':20} and nodes==13551
assert (largest,leaves)==(6221,2080) and stats_leaf=={'word':184,'cubic':56,'K2':56}
print('Signed chart tests',stats,'nodes',nodes,'largest',largest,'complete signed leaves',leaves,'final tests',stats_leaf)
