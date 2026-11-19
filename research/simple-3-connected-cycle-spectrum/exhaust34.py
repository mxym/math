"""Loop-free core ear census, no cubic restriction, all connected (multi)edges retained."""
from collections import defaultdict,Counter
from itertools import combinations,combinations_with_replacement
def path_count(n,E,s,t,budget=None):
 A=[[] for i in range(n)]
 for x,y in E:A[x].append(y);A[y].append(x)
 def go(v,seen,allowed):
  if v==t:return 1
  seen|=1<<v;c=0
  for w in A[v]:
   if seen>>w&1:continue
   c+=go(w,seen,allowed-c)
   if c>allowed:break
  return c
 return go(s,0,10**9 if budget is None else budget)
def adj(n,E):
 A=[[]for _ in range(n)]
 for x,y in E:A[x].append(y);A[y].append(x)
 return A
def c3(A):
 n=len(A)
 if n<4 or min(map(len,A))<3:return False
 for r in (0,1,2):
  for bad in combinations(range(n),r):
   q=[next(i for i in range(n) if i not in bad)];seen=set(bad)|{q[0]}
   while q:
    for j in A[q.pop()]:
     if j not in seen:seen.add(j);q.append(j)
   if len(seen)!=n:return False
 return True
def label(n,E):
 A=adj(n,E);M=[Counter(ns) for ns in A]
 C=[tuple(sorted(m.values())) for m in M];D={c:i for i,c in enumerate(sorted(set(C)))};C=[D[c] for c in C]
 for _ in range(n):
  v=[(C[i],tuple(sorted((C[j],m) for j,m in M[i].items()))) for i in range(n)]
  D={c:i for i,c in enumerate(sorted(set(v)))};nc=[D[c] for c in v]
  if nc==C:break
  C=nc
 return (tuple(sorted(v)),C,M)
def iso(r,s):
 _,C,M=r;_,D,N=s;n=len(C)
 opt=[{j for j in range(n) if C[i]==D[j]} for i in range(n)]
 def sub(L):
  if not L:return True
  i=min(L,key=lambda u:len(L[u]))
  for j in L[i]:
   T={u:{v for v in L[u] if v!=j and M[i][u]==N[j][v]} for u in L if u!=i}
   if all(T.values()) and sub(T):return True
  return False
 return sub(dict(enumerate(opt)))
def kids(n,E):
 # A negative index encodes a pre-existing vertex. Other indices encode literal edge copies.
 for i,j in combinations_with_replacement(range(-n,len(E)),2):
  if i<0 and i==j: continue
  F=[e for h,e in enumerate(E) if h!=i and h!=j]
  N=n
  if i<0:s=~i
  else:
   s=N;N+=1;a,b=E[i]
   if i!=j:F.extend([(a,s),(s,b)])
  if j<0:t=~j
  else:
   t=N;N+=1;c,d=E[j]
   if i==j:F.extend([(c,s),(s,t),(t,d)])
   else:F.extend([(c,t),(t,d)])
  yield N,tuple(sorted(tuple(sorted(e)) for e in F)),s,t
def census(limit):
 groups=[(2,((0,1),)*3,3)];rank=2;W={};tot=Counter()
 while groups:
  prev=groups;grp=defaultdict(list);ns=Counter();simp=Counter()
  cand=set()
  for n,E,k in prev:
   ns[n]+=1
   if len(E)==len(set(E)) and c3(adj(n,E)):
    simp[n]+=1;W.setdefault(k,(n,E));tot[k]+=1
   if k==limit:continue
   for N,F,s,t in kids(n,E):
    G=tuple(sorted(F+(tuple(sorted((s,t))),)))
    # Deduplicate identical labeled children before exact isomorphism.
    if G in cand:continue
    cand.add(G);step=path_count(N,F,s,t,limit-k)
    if k+step>limit:continue
    cs=label(N,G);q=grp[N,k+step,cs[0]]
    if not any(iso(cs,ss) for _,ss in q):q.append((G,cs))
  print(rank,len(prev),sum(simp.values()),'by order',sorted(ns.items()),flush=True)
  groups=[(n,E,k) for (n,k,_),v in grp.items() for E,_ in v];rank+=1
 return W,tot
if __name__=='__main__':
 import json,sys
 k=34; W,T=census(k)
 print('missing',sorted(set(range(1,k+1))-set(W)))
 missing=list(range(1,7))+list(range(8,13))+list(range(16,21))+[27,30,32,33,34]
 if sorted(set(range(1,k+1))-set(W))!=missing: raise ArithmeticError('unexpected census')
