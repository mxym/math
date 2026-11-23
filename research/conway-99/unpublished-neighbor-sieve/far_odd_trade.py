"""No actual far trade at rank <=4 over F5: exact signed signature atlas, Python/NumPy."""
import numpy as np,itertools as it
from collections import Counter
def inv(A):
 d=len(A);B=np.column_stack([A.copy()%5,np.eye(d,dtype=int)])
 for j in range(d):
  p=next((p for p in range(j,d) if B[p,j]),None)
  if p is None:return
  B[[p,j]]=B[[j,p]];B[j]=B[j]*pow(int(B[j,j]),-1,5)%5
  for k in range(d):
   if k!=j:B[k]=(B[k]-B[k,j]*B[j])%5
 return B[:,d:]
def clique(V,compat,fn,curr=(),exc=frozenset()):
 if not V and not exc:fn(curr);return
 if not V:return
 u=max(V|exc,key=lambda u:len(V&compat[u]))
 for v in sorted(V-compat[u]):
  clique(V&compat[v],compat,fn,curr+(v,),exc&compat[v]);V=V-{v};exc=exc|{v}
for d in range(2,5):
 P=list(it.combinations(range(d),2));pm=list(it.permutations(range(d)));sw=list(it.product((1,-1),repeat=d))
 v=np.array([t for t in it.product((-1,0,1),repeat=d) if next((y for y in t if y),0)==1]);seen=set();histo=Counter();maxsize=0;alls=[]
 for sig in it.product((-1,0,1),repeat=len(P)):
  A=np.zeros((d,d),int)
  for j,(r,t) in enumerate(P):A[r,t]=A[t,r]=sig[j]
  I=inv(A)
  if I is None:continue
  key=min(tuple(s[j]*s[k]*A[p[j],p[k]] for j,k in P) for s in sw if s[0]==1 for p in pm)
  if key in seen:continue
  seen.add(key);w=v[np.sum(v*(v@I),1)%5==0];BB=(w@I@w.T+2)%5-2
  base={next(j for j,a in enumerate(w) if np.array_equal(a,b) or np.array_equal(a,-b)) for b in A}
  compat={i:{j for j in range(len(w)) if abs(BB[i,j])<=1 and i!=j} for i in range(len(w))}
  ok=set.intersection(*(compat[i] for i in base));ml=[]
  clique(ok,compat,lambda t:ml.append(sorted(set(t)|base)))
  alls+=[(m,w[m].tolist(),BB[np.ix_(m,m)].tolist(),[m.index(b) for b in base]) for m in ml]
  histo+=Counter(len(m) for m in ml)
 print('d,maximal groups',d,len(seen),histo,flush=True)
 ct=Counter();extra=0
 for mm,li,pa,ba in alls:
  w=np.array(li);B=np.array(pa);mag=len(w);vv=np.r_[w,-w];F0=np.block([[B,-B],[-B,B]])
  for start in range(0,1<<(2*mag),8192):
   st=np.arange(start,min(1<<(2*mag),start+8192))[:,None];xs=(st>>np.arange(2*mag))&1
   ok=np.all(xs@vv==0,axis=1)
   for b in ba:ok&=(xs[:,b]+xs[:,b+mag]>0)
   for x in xs[ok]:
    ix=np.where(x)[0];F=F0[np.ix_(ix,ix)];r=np.abs(F).sum(1)
    ct['zero']+=1
    if np.any(r<6) or np.any(r>16) or np.any(F.sum(1)):continue
    ct['deg']+=1;p=(F>0).astype(int);n=(F<0).astype(int)
    HC=2-np.maximum(p+p@p,n+n@n);np.fill_diagonal(HC,0)
    if np.min(HC)<0 or np.trace(F@F@F):continue
    ct['angle']+=1
    if any(HC[np.ix_(np.where(F[i]>0)[0],np.where(F[i]<0)[0])].sum()<3*r[i] for i in range(len(F))):continue
    ct['words']+=1
    ck=[]
    for a,b in it.combinations(range(len(F)),2):
     if F[a,b]:continue
     K=np.zeros_like(F);K[a,b]=K[b,a]=1
     if all(np.triu(g@g+g,1).max()<=2 for g in (p+K,n+K)):ck.append((a,b))
    if np.array_equal(p@p,n@n) and sorted(v for t in ck for v in t)==list(range(len(F))) and all(np.array_equal(F[a],-F[b]) for a,b in ck) and (abs(F)@abs(F)@abs(F)).trace()>0:
     ct['old']+=1;continue
    raise AssertionError('Unexpected new terminal chart')
 target={2:(1,0,0,0),3:(40,14,0,0),4:(11322,387,316,8)}[d]
 assert tuple(ct[k] for k in ('zero','deg','angle','words'))==target and ct['old']==target[-1]
 print('terminal',d,ct,flush=True)
# Ternary isometry normal forms; the large auxiliary prime is only a safe relaxation.
import itertools as it,numpy as np
from collections import Counter
def rank(A,p):
 B=A.copy()%p;i=0;k=[]
 for j in range(B.shape[1]):
  t=next((t for t in range(i,len(B)) if B[t,j]),None)
  if t is None:continue
  B[[i,t]]=B[[t,i]];B[i]=B[i]*pow(int(B[i,j]),-1,p)%p
  for r in range(len(B)):
   if r!=i:B[r]=(B[r]-B[r,j]*B[i])%p
  k.append(j);i+=1
 return B,k
def go(dia):
 d=len(dia);v=np.array([k for k in it.product((-1,0,1),repeat=d) if next((x for x in k if x),0)>0 and sum(x*y*y for x,y in zip(dia,k))%3==0],int);n=len(v)
 if not n:return
 F=(v@np.diag(dia)@v.T+1)%3-1
 def action(x):
  return tuple(next(i for i,t in enumerate(v) if np.array_equal(w,t) or np.array_equal(w,-t)) for w in x)
 gen=[]
 for i in range(d):
  w=v.copy();w[:,i]*=-1;gen.append(action(w))
  if i and dia[i-1]==dia[i]:
   w=v.copy();w[:,[i-1,i]]=w[:,[i,i-1]];gen.append(action(w))
 pms=[]
 for p in gen:
  dims=np.arange(1<<n)
  pms.append(sum(((dims>>j)&1)<<p[j] for j in range(n)))
 seen=set();ct=Counter();sol=[];prime=1000003
 for m in range(1,1<<n):
  if m in seen:continue
  dfs=[m];seen.add(m)
  while dfs:
   x=dfs.pop()
   for g in pms:
    b=int(g[x])
    if b not in seen:seen.add(b);dfs.append(b)
  I=np.flatnonzero((m>>np.arange(n))&1);w=v[I]
  if len(rank(w,3)[1])<d:continue
  ct['masks']+=1;B=F[np.ix_(I,I)];R,piv=rank(B,prime);free=[j for j in range(len(I)) if j not in piv]
  for f in it.product((-1,0,1),repeat=len(free)):
   m0=np.zeros(len(I),int);m0[free]=f
   if free:m0[piv]=(-R[:len(piv),free]@m0[free]+1)%prime-1
   if np.max(m0)>1 or np.min(m0)<-1 or np.any(B@m0):continue
   ct['orient']+=1
   j=np.r_[np.where(m0>=0)[0],np.where(m0<=0)[0]];sg=np.r_[np.ones((m0>=0).sum(),int),-np.ones((m0<=0).sum(),int)]
   E=B[np.ix_(j,j)]*sg[:,None]*sg[None,:]
   r=abs(E).sum(1)
   if r.min()<6 or r.max()>16:continue
   ct['deg']+=1;p=(E>0).astype(int);q=(E<0).astype(int);cap=2-np.maximum(p+p@p,q+q@q);np.fill_diagonal(cap,0)
   if cap.min()<0 or np.trace(E@E@E):continue
   ct['angle']+=1
   if any(cap[np.ix_(E[i]>0,E[i]<0)].sum()<3*r[i] for i in range(len(E))):continue
   ct['words']+=1;ck=[]
   for i,j in it.combinations(range(len(E)),2):
    if E[i,j]:continue
    K=np.zeros_like(E);K[i,j]=K[j,i]=1
    if all(np.triu(t@t+t,1).max()<=2 for t in (p+K,q+K)):ck.append((i,j))
   if np.array_equal(p@p,q@q) and sorted(y for x in ck for y in x)==list(range(len(E))) and all(np.array_equal(E[i],-E[j]) for i,j in ck) and np.trace(abs(E)@abs(E)@abs(E))>0:ct['old']+=1;continue
   sol.append((E.tolist(),ck))
 assert not sol
 target={(2,2):(1,1,0,0,0),(3,1):(2,2,1,0,0),(3,2):(2,2,1,0,0),(4,1):(502,2378,1064,195,1),(4,2):(47,57,50,4,0)}[d,dia[-1]]
 assert tuple(ct[k] for k in ('masks','orient','deg','angle','words'))==target and ct['old']==target[-1]
 print(dia,n,ct,flush=True)
for d in (2,3,4):
 for c in (1,2):go([1]*(d-1)+[c])

# Six-minor lift at every prime >=7 (for p>=13, Hadamard suffices).
"""Exact minor lift and rank-four trade exclusion for the fixed 60 far contact words.
Python 3 + NumPy; no floating point or external solver.
"""

from itertools import combinations,product,permutations
from collections import Counter
import numpy as np
V=range(6);P=list(combinations(V,2));pos={s:i for i,s in enumerate(P)}
def det(A):
 B=[list(map(int,row)) for row in A];sign=1;d=1
 for j in range(5):
  i=next((i for i in range(j,6) if B[i][j]),None)
  if i is None:return 0
  if i!=j:B[i],B[j]=B[j],B[i];sign=-sign
  p=B[j][j]
  for k in range(j+1,6):
   for l in range(j+1,6):B[k][l]=(p*B[k][l]-B[k][j]*B[j][l])//d
  d=p
 return sign*B[5][5]
perm=[[pos[tuple(sorted((p[a],p[b])))] for a,b in P] for p in permutations(V)]
used=set();counts=Counter();out=[];feas=[];patterns=Counter()
S=np.array(list(product((1,-1),repeat=5)));S=np.column_stack((np.ones(32,int),S))
for mask in range(1<<15):
 if mask in used:continue
 idx=[i for i in range(15) if mask>>i&1]
 used.update(sum(1<<p[i] for i in idx) for p in perm);counts['graphs']+=1
 comp=list(V);F=[];other=[]
 for q in idx:
  i,j=P[q];a,b=comp[i],comp[j]
  if a!=b:comp=[a if c==b else c for c in comp];F.append(q)
  else:other.append(q)
 B=np.zeros((6,6),int)
 for q in F:i,j=P[q];B[i,j]=B[j,i]=1
 for x in range(1<<len(other)):
  counts['signed']+=1
  for k,q in enumerate(other):i,j=P[q];B[i,j]=B[j,i]=1-2*(x>>k&1)
  dt=det(B)
  if not dt or (dt%49 and dt%121):continue
  raise AssertionError((B.tolist(),dt))
assert counts=={'graphs':156,'signed':4562}
print('All 4562 signed six-site tests passed:',counts)
