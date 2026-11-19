#!/usr/bin/env python3
"""Exact checks; the proof (not these finite replays) covers arbitrary graph orders. Python standard library."""
from math import gcd
from itertools import product
from random import Random
from fractions import Fraction as F

def req(msg,a):
 if not a: raise ArithmeticError(msg)
def sig(A):
 A=[row[:] for row in A]
 ans=0
 while A:
  n=len(A); diag=next((i for i in range(n) if A[i][i]),None)
  if diag is not None:
   i=diag; v=A[i][i]; s=1 if v>0 else -1;ans+=s
   rest=[j for j in range(n) if j!=i]
   B=[[abs(v)*A[j][k]-s*A[j][i]*A[k][i] for k in rest] for j in rest]
  else:
   edge=next(((j,k) for j in range(n) for k in range(j) if A[j][k]),None)
   if edge is None:return ans
   j,k=edge; v=A[j][k]; s=1 if v>0 else -1;rest=[a for a in range(n) if a not in (j,k)]
   B=[[abs(v)*A[a][b]-s*(A[a][j]*A[k][b]+A[a][k]*A[j][b]) for b in rest] for a in rest]
  g=0
  for row in B:
   for x in row:g=gcd(g,x)
  A=[[v//g for v in row] for row in B] if g>1 else B
 return ans

def runpaths(b,paths,marks=()):
 """Build fresh internals. Duplicate direct edges and loops allowed only if internally subdivided."""
 n=b; E=[]
 for i,j,l in paths:
  p=[i,*range(n,n+l-1),j];n+=l-1;E.extend(zip(p,p[1:]))
 for i in marks:E.append((i,n));n+=1
 req('no loops',all(i!=j for i,j in E))
 req('simple',len(E)==len(set(tuple(sorted(x)) for x in E)))
 return n,E
def mat(n,E,root=None):
 A=[[0]*n for _ in range(n)]
 for i in range(n):A[i][i]=-2
 for i,j in E:A[i][j]+=1;A[j][i]+=1;A[i][i]+=1;A[j][j]+=1
 if root is not None:A[root][root]+=1
 return A
def principal(A,inds):
 return [[A[i][j] for j in inds] for i in inds]
def perm_catalog():
 """All rooted unlabelled trees up through eight vertices, AHU-type tuple rooted representation."""
 from itertools import combinations_with_replacement
 trees={1:[()]}
 for n in range(2,9):
  old=[(k,t) for k in trees for t in trees[k]]; out=[]
  def add(b,start,L):
   if not b:out.append(tuple(L));return
   for idx in range(start,len(old)):
    k,t=old[idx]
    if k>b:break
    add(b-k,idx,L+[t])
  add(n-1,0,[]);trees[n]=out
 return trees
def evaluate(t):
 children=[evaluate(f) for f in t]
 x=-1+sum((1-g for _,g in children),F(0));req('nonzero',bool(x))
 return sum(a for a,_ in children)+(1 if x<0 else -1),1/x
def edgetree(t):
 E=[];n=1
 def rec(t,r):
  nonlocal n
  for c in t:
   j=n;n+=1;E.append((r,j));rec(c,j)
 rec(t,0);return n,E
def checkbranches():
 c=0
 for n,ts in perm_catalog().items():
  for t in ts:
   nn,E=edgetree(t);B=mat(n,E,0);cost,g=evaluate(t)
   req("tree shapes",nn==n);req("tree inertia",-cost==sig(B))
   req("budgets",cost>=0 and (cost!=0 or g>=1) and (cost!=1 or g>=-1))
   for d in [-5,-2,-1,0,1,2,5]:
    C=[q[:] for q in B]
    for row in C:row.append(0)
    C.append([0]*(n+1));C[-1][-1]=d+1;C[-1][0]=C[0][-1]=1
    opt=(1 if d+2>0 else (-1 if d+2<0 else 0))-1 if cost==1 else (1 if d>0 else (-1 if d<0 else 0))
    req("host domination",sig(C)<=opt)
   c+=1
 print("PASS rooted trees of orders 1-8, direct rational/integer signature and seven scalar boundaries each:",c)
def quotient(b,paths,marks=()):
 """Direct signed constraint elimination on bare internal paths."""
 B=[[0]*b for _ in range(b)];adj=[[] for _ in range(b)]
 for i in range(b):B[i][i]=-2+2*(i in marks)
 for i,j,L in paths:
  B[i][i]+=1;B[j][j]+=1
  if L%2:
   s=1 if L%4==1 else -1
   B[i][j]+=s;B[j][i]+=s
  else:
   s=1 if L%4==0 else -1
   adj[i].append((j,s));adj[j].append((i,s))
 label=[None]*b;groups=[]
 for i in range(b):
  if label[i] is not None:continue
  stack=[i];label[i]=1;ok=True;group=[]
  while stack:
   v=stack.pop();group.append(v)
   for j,s in adj[v]:
    h=label[v]*s
    if label[j] is None:label[j]=h;stack.append(j)
    elif label[j]!=h:ok=False
  if ok:groups.append(group)
 C=[[sum(label[i]*B[i][j]*label[j] for i in g for j in h) for h in groups] for g in groups]
 return sig(C)-len(marks)
def checkpaths():
 rng=Random(221);count=0
 for scheme in [[(0,0),(0,0)],[(0,1)]*3,[(0,0),(0,1),(1,1)],[(0,0),(0,1),(1,2),(1,3),(2,3),(2,3),(3,3)]]:
  b=1+max(max(ij) for ij in scheme)
  for lengths in product(range(3,7),repeat=len(scheme)) if len(scheme)<=3 else [tuple(rng.randrange(3,7) for e in scheme) for _ in range(190)]:
   paths=[(i,j,l) for (i,j),l in zip(scheme,lengths)]
   for marks in [(),tuple(j for j in range(b) if rng.getrandbits(1))]:
    n,E=runpaths(b,paths,marks);a=sig(mat(n,E));req("signed quotient",a==quotient(b,paths,marks))
    req("interlacing",a<=b-len(marks))
    if 1<=len(paths)-b+1<=5:req("cyclomatic bound",2*a<=3*(len(paths)-b+1)-1)
    count+=1
 print("PASS singular/unsigned path expansion, coincident endpoints and parallel paths:",count)
def checkround():
 rng=Random(201);ct=0
 # Arbitrary underlier, singular hosts allowed. Mixed runs with coincident ends.
 for m in range(1,15):
  for same in [False,True]:
   for t in range(25):
    b=4;B=[[0]*b for _ in range(b)]
    for i in range(b):
     for j in range(i+1):B[i][j]=B[j][i]=rng.randint(-2,2)
    u,v=0,0 if same else 1
    A=[r+[0]*m for r in B]+[[0]*(b+m) for _ in range(m)]
    for j in range(b,b+m):A[j][j]=2
    vs=[u,*range(b,b+m),v]
    for i,j in zip(vs,vs[1:]):A[i][j]+=1;A[j][i]+=1
    e=(-1)**m;B[u][v]+=e;B[v][u]+=e
    req("round",sig(A)-m<=sig(B));ct+=1
 print("PASS exact marked-path Loewner consequence, including loop terminals:",ct)
if __name__=='__main__':checkbranches();checkround();checkpaths()
