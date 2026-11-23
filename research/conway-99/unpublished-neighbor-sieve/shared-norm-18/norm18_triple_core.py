# Exact finite rejection of the 38 marked sites in an all-dot-seven triple.
# Run: python norm18_triple_core.py [zero-based chart IDs, optional]
import numpy as np
from itertools import combinations,permutations,product
from functools import lru_cache
from math import prod
lab=list(combinations(range(4),2))
def partitions():
 def go(rr,g):
  if not rr:yield g;return
  a=min(rr)
  for b in sorted(rr-{a}):yield from go(rr-{a,b},g+((a,b),))
 return list(go(set(range(6)),()))
def leaflist(part,i):
 l,m=part[i];Q=sorted(lab[l]+lab[m]);res=set()
 for pp in set(permutations(Q)):
  if pp[0]==pp[1] or pp[2]==pp[3] or pp[0]>pp[1] or pp[2]>pp[3]:continue
  res.add(tuple([(i,q,l if j<2 else m)for j,q in enumerate(pp)]))
 return sorted(res)
@lru_cache(None)
def reps():
 result={}
 for part in partitions():
  for fs in product(*(leaflist(part,i)for i in range(3))):
   def code(p):
    return tuple(sorted(tuple(sorted((tuple(sorted(p[a]for a in lab[l])),tuple(sorted(p[q]for _,q,x in f if x==l)))for l in part[i]))for i,f in enumerate(fs)))
   c=min(code(p)for p in permutations(range(4)))
   if c not in result:result[c]=(part,sum(fs,()))
 return sorted(result.items())

def nside(part,fs,i):
 K,_=core23(part,fs)
 # indices in K: 0 root,1..4 Q,5..10 labels,11..22 singles; choices exclusive positive Pi+two other L groups
 cols=[11+k for k,(j,_,_) in enumerate(fs)if i==j]+[5+l for j in range(3)if j!=i for l in part[j]]
 adj=[set(np.flatnonzero(r))for r in K]
 tar=[3]*4+[2]*4;cap={(j,k):2-int(K[cols[j],cols[k]])-len(adj[cols[j]]&adj[cols[k]]) for j,k in combinations(range(8),2)}
 # 23 core must already obey every actual pair cap
 if any(len(v&adj[k])>2-(k in v)for j,v in enumerate(adj)for k in range(j)):return
 R=[]
 for k in combinations(range(8),4):
  vv={cols[j]for j in k}
  if not all(len(vv&v)<=2-int(h in vv)for h,v in enumerate(adj)):continue
  if not all(cap[j,l]>=1 for j,l in combinations(k,2)):continue
  R.append((sum(1<<j for j in k),k))
 def go(start,rows):
  left=5-len(rows)
  if not left:
   assert not any(tar)
   yield tuple(sorted(rows));return
  if max(tar)>left:return
  for st in range(start,len(R)):
   v,k=R[st]
   if not all(tar[j]>0 for j in k) or any((v&u).bit_count()>2 for u in rows):continue
   if not all(cap[j,l]>0 for j,l in combinations(k,2)):continue
   for j in k:tar[j]-=1
   for j,l in combinations(k,2):cap[j,l]-=1
   yield from go(st+1,rows+(v,))
   for j in k:tar[j]+=1
   for j,l in combinations(k,2):cap[j,l]+=1
 yield from go(0,())

def core23(part,fs):
 # Site order: o, four q, six pair centers, twelve single leaves.
 A=np.zeros((23,23),dtype=np.int64)
 def edge(i,j): A[i,j]=A[j,i]=1
 for q in range(4): edge(0,1+q)
 for l,p in enumerate(lab):
  for q in p: edge(5+l,1+q)
 for k,(_,q,l) in enumerate(fs):
  edge(11+k,1+q); edge(11+k,5+l)
 T=np.array([[1]+[-1]*4+[int(l not in part[i]) for l in range(6)]
             +[int(j==i) for j,q,l in fs] for i in range(3)],dtype=np.int64)
 return A,T
def incidence(part,fs,i,rows):
 cols=[11+k for k,(j,q,l) in enumerate(fs) if j==i]+[5+l for j in range(3) if j!=i for l in part[j]]
 return np.array([[int(v in cols and bool(r & (1<<cols.index(v)))) for r in rows] for v in range(23)],dtype=np.int64)
def psd(G):
 # Exact symmetric fraction-free elimination. Work on the upper triangle.
 # At each step the remaining array is a POSITIVE multiple of the Schur complement.
 a=[[int(x) for x in row] for row in G];prev=1
 for k,row in enumerate(a):
  p=row[k]
  if p<0:return False
  if p==0:
   if any(row[k+1:]):return False
   continue
  for i in range(k+1,len(a)):
   rr=a[i];q=row[i]
   for j in range(i,len(a)):
    v=p*rr[j]-q*row[j]; rr[j],rem=divmod(v,prev);assert rem==0
  prev=p
 return True
@lru_cache(None)
def tables(r,c):
 if not r:return ((),) if not any(c) else ()
 return tuple((t,)+m for t in combinations([j for j in range(len(c))if c[j]],r[0])for m in tables(r[1:],tuple(x-int(j in t) for j,x in enumerate(c))))
def search(target):
 _,(part,fs)=reps()[target];a,t=core23(part,fs);C=23
 roles=[]
 for i in range(3):
  g=[]
  for row in nside(part,fs,i):
   M=incidence(part,fs,i,row);g.append((M,M@M.T,t@M))
  roles.append(g)
 basecap=12*np.eye(C,dtype=int)+2-a-a@a;st=[0]*6
 for rr in product(*roles):
  st[0]+=1
  if np.min(basecap-rr[0][1]-rr[1][1]-rr[2][1])<0:continue
  if any(sum(rr[j][1][5+part[i][0],5+part[i][1]] for j in range(3))+len(set(lab[part[i][0]])&set(lab[part[i][1]]))!=2 for i in range(3)):continue
  st[1]+=1
  B=np.concatenate([r[0]for r in rr],axis=1)
  if np.any((B.T@B-2)*(1-np.eye(15,dtype=int))>0):continue
  st[2]+=1
  ps=list(combinations(range(3),2));kinds=[]
  for i,j in ps:
   kk=[]
   for table in tables(tuple(rr[i][2][j]),tuple(rr[j][2][i])):
    Sx=np.zeros((5,5),int)
    for h,inds in enumerate(table):Sx[h,list(inds)]=1
    # check pair common cap between C,Ni or Nj and Ni&Nj
    if np.any((rr[i][0].T@rr[j][0]+Sx)>2):continue
    if np.any(a@rr[i][0]+rr[j][0]@Sx.T+rr[i][0]>2)or np.any(a@rr[j][0]+rr[i][0]@Sx+rr[j][0]>2):continue
    kk.append(Sx)
   kinds.append(kk)
  if any(len(g)==0 for g in kinds):continue
  st[3]+=1
  for pp in product(*kinds):
   X=np.zeros((15,15),int)
   for (i,j),u in zip(ps,pp):X[5*i:5*i+5,5*j:5*j+5]=u;X[5*j:5*j+5,5*i:5*i+5]=u.T
   A=np.block([[a,B],[B.T,X]])
   F=12*np.eye(38,dtype=int)+2-A-A@A
   if np.min(F)<0:continue
   st[4]+=1
   DD=14-A.sum(0);Y=61*F-np.outer(DD,DD)
   if psd(Y):
    st[5]+=1
    print("SURVIVOR",target,st,flush=True)
    return st
 return st

if __name__=='__main__':
 import sys
 ids=list(map(int,sys.argv[1:]))or list(range(34))
 assert len(partitions())==15
 assert sum(prod(len(leaflist(p,i)) for i in range(3)) for p in partitions())==424
 assert len(reps())==34
 expected=[1406,1406,1728,1728,5008,5222,1728,1728,1406,5439,0,0,0,0,0,0,1728,0,0,0,0,1406,1728,5656,216,0,216,0,216,216,0,0,0,0]
 for i in ids:
  assert 0<=i<34
  z=search(i);print(i,*z,flush=True);assert z[-2:]==[expected[i],0]
