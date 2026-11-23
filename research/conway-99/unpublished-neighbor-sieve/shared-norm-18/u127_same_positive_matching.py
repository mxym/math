
from itertools import product,combinations,permutations
from collections import Counter
from math import comb

q=7
def maketree(seq,n):
 deg=[1]*n
 for v in seq:deg[v]+=1
 E=[]
 for v in seq:
  leaf=next(i for i,vv in enumerate(deg) if vv==1)
  E.append(tuple(sorted((leaf,v))))
  deg[leaf]-=1;deg[v]-=1
 E.append(tuple(i for i,vv in enumerate(deg) if vv==1))
 return tuple(sorted(E))
def trees(n):
 if n==1:return [()]
 D={}
 for seq in product(range(n),repeat=n-2):
  E=maketree(seq,n)
  A=[set() for i in range(n)]
  for u,v in E:A[u].add(v);A[v].add(u)
  def sig(r,p):return '('+''.join(sorted(sig(z,r) for z in A[r] if z!=p))+')'
  D.setdefault(min(sig(i,-1) for i in range(n)),E)
 return list(D.values())
def shapes():
 for a in (1,2,3):
  for X,Y in product(trees(a),trees(7-a)):
   E=X+tuple((i+a,j+a) for i,j in Y)
   A=[set() for _ in range(7)]
   for u,v in E:A[u].add(v);A[v].add(u)
   if sum(len(z)**2 for z in A)>20:continue
   yield E,A
def contacts(E,A):
 deg=[len(a) for a in A]
 pairs=list(combinations(range(q),2)); ix={x:i for i,x in enumerate(pairs)}
 cap=[2-int(v in A[u])-len(A[u]&A[v]) for u,v in pairs]
 T=[z for z in combinations(range(q),3) if sum(deg[u] for u in z)<=5 and all(len(set(z)&A[u])<=2-int(u in z) for u in range(q)) and all(cap[ix[e]]>0 for e in combinations(z,2))]
 ptr={z:tuple(ix[e] for e in combinations(z,2)) for z in T}
 rem=[x+2 for x in deg]
 es=set(E)
 autos=[p for p in permutations(range(q)) if all(deg[j]==deg[p[j]] for j in range(q)) and all(tuple(sorted((p[u],p[v]))) in es for u,v in E)]
 transm=[[T.index(tuple(sorted(p[j] for j in t))) for t in T] for p in autos]
 cns=Counter()
 def rec(i,V):
  p=len(V)
  if p==8:
   if any(rem):return
   if tuple(V)!=min(tuple(sorted(v[z] for z in V)) for v in transm):return
   cns['forms']+=1
   yield tuple(T[j] for j in V)
   return
  if len(T)-i<8-p:return
  if max(rem)>8-p:return
  D=[sum(u in t for t in T[i:]) for u in range(q)]
  if any(rem[u]>D[u] for u in range(q)):return
  for k in range(i,len(T)):
   t=T[k]
   if any(rem[u]==0 for u in t):continue
   if any(cap[e]==0 for e in ptr[t]):continue
   for u in t:rem[u]-=1
   for e in ptr[t]:cap[e]-=1
   yield from rec(k+1,V+[k])
   for e in ptr[t]:cap[e]+=1
   for u in t:rem[u]+=1
 yield from rec(0,[])
G=[(E,A,list(contacts(E,A))) for E,A in shapes()]
for E,A,B in G: print(E,sorted(map(len,A)),len(B),flush=True)
print('TOTAL',sum(len(B) for E,A,B in G))

assert len(G)==7 and sum(len(v) for _,_,v in G)==32
assert [(E,len(v)) for E,_,v in G if v]==[(((0,1),(0,2),(3,4),(3,5),(4,6)),32)]
