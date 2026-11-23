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
  if not dt or dt%49:continue
  raise AssertionError((B.tolist(),dt))
assert counts=={'graphs':156,'signed':4562}
print('All 4562 signed six-site tests passed:',counts)

import numpy as np,itertools as it
from collections import Counter
V=range(4);P=list(it.combinations(V,2));M=lambda s:sum(1 for t in s)
def gram(sig):
 A=np.zeros((4,4),int)
 for (j,k),x in zip(P,sig):A[j,k]=A[k,j]=x
 return A
v=np.array([x for x in it.product((-1,0,1),repeat=4) if next((y for y in x if y),0)>0])
sw=np.array(list(it.product((1,-1),repeat=3)));sw=np.column_stack((np.ones(8,int),sw));pms=list(it.permutations(V))
def key(A):
 return min(tuple(A[p[j],p[k]]*s[j]*s[k] for j,k in P) for s in sw for p in pms)

def det4(A):
 from math import prod
 return sum((-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))*prod(int(A[i,p[i]]) for i in range(len(p))) for p in it.permutations(range(len(A))))
def adjugate(A):
 return np.array([[(-1)**(i+j)*det4(np.delete(np.delete(A,j,axis=0),i,axis=1)) for j in range(len(A))] for i in range(len(A))],int)
stats=Counter();seen=set();maxlines=0
for sig in it.product((0,1,-1),repeat=6):
 A=gram(sig);dt=det4(A)
 if dt<=0:continue
 k=key(A)
 if k in seen:continue
 seen.add(k);D=adjugate(A);assert np.array_equal(A@D,dt*np.eye(4,dtype=int));w=v[np.sum(v*(v@D),1)==0];B=w@D@w.T
 ok=(abs(B)==dt)|(B==0)

 idx=lambda b:next(i for i in range(len(w)) if np.array_equal(b,w[i]) or np.array_equal(-b,w[i]))
 base={idx(b) for b in A};good={i for i in range(len(w)) if all(ok[i,j] for j in base)}-base
 ml=[]
 for q in range(len(good)+1):
  for ds in it.combinations(good,q):
   if all(ok[a,b] for a,b in it.combinations(ds,2)) and all(not all(ok[a,b] for b in ds) for a in good-set(ds)):
    code=w[sorted(base|set(ds))]
    mag=len(code);maxlines=max(maxlines,mag);vs=np.concatenate((code,-code));pair=(vs@D@vs.T)//dt
    n0=1<<(2*mag)
    states=np.arange(n0,dtype=np.int32)[:,None];xs=((states>>np.arange(2*mag))&1).astype(np.int16)
    use=np.all(xs@vs==0,axis=1)
    for ii,idx0 in enumerate(sorted(base|set(ds))):
     if idx0 in base:use &= (xs[:,ii]+xs[:,ii+mag])>0
    xs=xs[use]
    stats['zero']+=len(xs)
    for x in xs:
     S0=np.where(x)[0];F=pair[np.ix_(S0,S0)];r=np.abs(F).sum(1)
     if np.any(r<6) or np.any(r>16):continue
     stats['deg']+=1
     p=(F>0).astype(int);m=(F<0).astype(int);HC=2-np.maximum(p+p@p,m+m@m);np.fill_diagonal(HC,0)
     if HC.min()<0:continue
     if np.trace((F@F)@F)!=0:continue
     stats['angular']+=1
     nS=len(F)
     if any(HC[np.ix_(np.where(F[i]==1)[0],np.where(F[i]==-1)[0])].sum()<6*(F[i]>0).sum() for i in range(nS)):continue
     stats['nearcap']+=1

     ck=[]
     for i,j in it.combinations(range(nS),2):
      if F[i,j]:continue
      K=np.zeros_like(F);K[i,j]=K[j,i]=1
      if all(np.triu(a@a+a,1).max()<=2 for a in (p+K,m+K)):ck.append((i,j))
     assert nS==18 and np.array_equal(p@p,m@m)
     assert sorted(i for e in ck for i in e)==list(range(nS))
     assert len(ck)==nS//2 and all(np.array_equal(F[i],-F[j]) for i,j in ck)
     assert (np.abs(F)@np.abs(F)@np.abs(F)).trace()>0
     stats['odd']+=1
    ml.append(mag)

 print(k,len(ml),stats,flush=True)
assert len(seen)==7 and maxlines==9 and stats=={'zero':11008,'deg':323,'angular':303,'nearcap':8,'odd':8}
print('No rank-four trade on fixed triangle contact words.',stats)
