"""Rank-36 B12 + flat 24-wing exclusion. Python standard library plus NumPy. No solver."""
from itertools import combinations
from collections import Counter
from fractions import Fraction

def rank(A):
 A=[[Fraction(x) for x in row] for row in A];r=0
 for j in range(len(A[0])):
  i=next((i for i in range(r,len(A)) if A[i][j]),None)
  if i is None:continue
  A[i],A[r]=A[r],A[i]
  for i in range(r+1,len(A)):
   q=A[i][j]/A[r][j];A[i]=[a-q*b for a,b in zip(A[i],A[r])]
  r+=1
 return r
P=(1,0,3,2);Q=(2,3,0,1);f=(0,3,2,1)
N=[set() for _ in range(12)]
for i in range(4):
 for a,b in [(i,P[i]),(4+i,4+Q[i]),(8+i,8+P[i]),(i,4+i),(4+i,8+i),(8+i,f[i])]:N[a].add(b);N[b].add(a)
h=(2,1,5,6,0,0,0,0,5,6,2,1)
assert sum(h)%7==0 and all((3*h[i]-sum(h[j] for j in N[i]))%7==0 for i in range(12))
M={(i,j):2-int(j in N[i])-len(N[i]&N[j])-int(i//4==j//4) for i,j in combinations(range(12),2)}

import numpy as np
from itertools import permutations
from math import prod
NI=np.array([0,1,4,5,2,3,6],np.int16)
def match(s):
 if not s:yield ()
 else:
  i=s[0]
  for j in s[1:]:
   for rest in match([x for x in s[1:] if x!=j]):yield ((i,j),)+rest
m=list(match(list(range(8))));id0=m[0];md={p:j for j,p in enumerate(m)}
stab=[p for p in permutations(range(8)) if all(abs(p[a]-p[b])==1 and p[a]//2==p[b]//2 for a,b in id0)]
def permM(p,M):
 return tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in M))
orb=np.array([[md[permM(p,M)] for M in m] for p in stab],np.int16)
def rep():
 used=set();ls=[]
 for i in range(105):
  for j in range(105):
   key=i*105+j
   if key in used:continue
   used.update((orb[:,i]*105+orb[:,j]).astype(int));ls.append((i,j))
 return ls
def invmat(A):
 A=np.array(A,np.int16)%7;n,m=A.shape;B=np.eye(n,dtype=np.int16);piv=[];det=1
 for j in range(m):
  i=len(piv);ns=np.where(A[i:,j]!=0)[0]
  if not len(ns):continue
  ij=i+ns[0];piv.append(j);det=det*int(A[ij,j])*(-1 if ij!=i else 1)%7
  for X in (A,B):
   X[[i,ij]]=X[[ij,i]]
  s=NI[A[i,j]]
  for X in (A,B):X[i]=X[i]*s%7
  coeff=A[:,j,None].copy();coeff[i]=0
  for X in (A,B):X[:]=(X-coeff*X[i])%7
 return piv,det,B
def umake(i,j):
 U=np.zeros((24,24),np.int16)
 for k,Mt in enumerate((id0,m[i],m[j])):
  for a,b in Mt:U[8*k+a,8*k+b]=U[8*k+b,8*k+a]=1
 for a in range(8):
  for b,c in combinations([a,a+8,a+16],2):U[b,c]=U[c,b]=1
 return U
V=np.zeros((12,12),np.int16)
for i in range(12):V[i,sorted(N[i])]=1
wing=np.r_[np.arange(12)//4,np.arange(24)//8];E0=[e for e,n in M.items() if n and sum(h[i] for i in e)%7==0]
def adjword(i,j,verbose=False):
 U=umake(i,j);U2=U@U;D=np.zeros((36,36),np.int16);D[:12,:12]=V;D[12:,12:]=U
 G=(3*np.eye(36,dtype=np.int16)-D+4)%7;rank,_,inv=invmat(G);assert len(rank)==34
 B0=invmat(G[np.ix_(rank,rank)])[2]
 # A near pair must occur on at least one far word, counts due to lambda/mu.
 cap=2-D-D@D-(wing[:,None]==wing[None,:]).astype(np.int16)
 W=[];where=[]
 for e in E0:
  sz=[2-sum(int(t//4==w) for t in e) for w in range(3)]
  deltas=[]
  from itertools import product
  for q in product(*[combinations(range(12+8*w,20+8*w),k) for w,k in enumerate(sz)]):
   s=e+sum(q,())
   if any(cap[a,b]<=0 for a,b in combinations(s,2)):continue
   deltas.append(s)
  tt=np.zeros((len(deltas),36),np.int16);tt[np.arange(len(tt))[:,None],np.array(deltas)]=1
  p=(4-tt[:,rank])%7;pr=p@B0%7
  ok=((p*pr).sum(1)%7==0)&np.all(tt+tt@D<=2,axis=1)
  rows=np.where(ok)[0];where.append((len(W),len(W)+len(rows)));W+=list(tt[rows])
 W=np.array(W);X=(4-W[:,rank])%7;pr=X@B0%7
 def adj(a,b):
  A=(4-pr[a]@X[b].T)%7
  n=W[a]@W[b].T
  ok=(A<=1)&(n<=2-A)
  for w in range(3):
   ix=np.where(wing==w)[0];ok &= ((W[a][:,ix]@W[b][:,ix].T)<=1)
  # If both words contain a near pair of capacity1, cannot coexist, even with disjoint wings.
  for t,z in zip(*np.where(np.triu(cap==1,1))):
   qa=np.where(W[a,t]&W[a,z])[0];qb=np.where(W[b,t]&W[b,z])[0]
   if len(qa)*len(qb):ok[np.ix_(qa,qb)]=False
  return A,ok
 return U,W,where,adj


def graph(i,j):
 U,W,where,adj=adjword(i,j);n=len(W);D=np.zeros((36,36),np.int16);D[:12,:12]=V;D[12:,12:]=U
 A=np.zeros((n,n),np.int16);OK=np.zeros((n,n),bool);slots=2-W-W@D
 grp=[list(range(a,b)) for a,b in where]
 for z in range(10):
  for t in range(z):
   g=grp[z];b=grp[t];a,ok=adj(g,b)
   # Each adjacent selected word must fit all 36 remaining near-contact demands of the other.
   ok &= (a==0)|((((slots[g]==0).astype(np.int16)@W[b].T)==0)&((W[g]@(slots[b]==0).T.astype(np.int16))==0))
   OK[np.ix_(g,b)]=ok;OK[np.ix_(b,g)]=ok.T
   A[np.ix_(g,b)]=a;A[np.ix_(b,g)]=a.T
 return U,W,A,OK,grp,slots
def solve(i,j):
 U,W,A,OK,grp,slots=graph(i,j)
 def bt(row):return int.from_bytes(np.packbits(row,bitorder='little').tobytes(),'little')
 bits=[bt(row) for row in OK];g=[sum(1<<int(j) for j in ll) for ll in grp];nodes=[0]*11;ex=[]
 def go(L,n,known):
  nodes[n]+=1
  if not L:ex.append(known);return True
  j=min(range(len(L)),key=lambda x:L[x].bit_count());w=L[j]
  others=L[:j]+L[j+1:]
  while w:
   b=w&-w;w-=b;ix=b.bit_length()-1
   rr=[v&bits[ix] for v in others]
   if all(rr) and go(rr,n+1,known+[ix]):return True
  return False
 yes=go(g,0,[]);return tuple(map(len,grp)),nodes,yes,ex[:1]
if __name__=="__main__":
 reps=rep()
 from collections import Counter
 tally=Counter();nodes=0;maxnodes=0
 assert len(stab)==384 and len(reps)==86
 for i,j in reps:
  U=umake(i,j);p,d,_=invmat((3*np.eye(24,dtype=np.int16)-U)[:-1,:-1])
  tally[d if len(p)==23 else 0]+=1
  if len(p)==23 and d in (3,5,6):
   g,v,ok,ex=solve(i,j);assert not ok;nodes+=sum(v);maxnodes=max(maxnodes,sum(v));print(i,j,g,sum(v))
 assert tally=={0:47,1:3,2:6,3:14,5:4,6:12}
 print('All 30 nonsquare-unit 24-representatives rejected; nodes',nodes,'max per case',maxnodes)
 assert maxnodes==173
