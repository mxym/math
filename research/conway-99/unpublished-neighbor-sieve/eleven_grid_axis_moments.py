"""Exact axis/profile screen for the four-cubic eleven-grid root.

All tests are necessary, not a reconstruction. K=simple; dO=opposite
doubles (1,3)+(1,3); dE=opposite doubles (2,2)+(2,2).
See eleven-grid-odd-doubled-exclusion.md for the graph identities and
the subsequent analytic exclusion of both surviving dO axis charts.
"""

from itertools import product,combinations,permutations
from collections import Counter
AX=range(7); P=set(combinations(AX,2)); C=range(4); T=range(4,7)
def edge(a,b):return tuple(sorted((a,b)))
base={
 'K':((0,1,2),(2,3,2),(0,2,3),(0,3,1),(1,2,1),(1,3,1)),
 'dO':((0,1,3),(0,1,1),(2,3,3),(2,3,1),(0,2,1),(1,3,1)),
 'dE':((0,1,2),(0,1,2),(2,3,2),(2,3,2),(0,2,1),(1,3,1)),
}
def hx(L,q):
 return tuple(sorted((*edge(q[a],q[b]),d)for a,b,d in L))
def gx(paths,pi):
 return tuple(sorted(min(tuple(pi[i]for i in p),tuple(pi[i]for i in p[::-1]))for p in paths))
def main(L):
 group=[p+q for p in permutations(C)for q in permutations(T)if hx(L,p)==tuple(sorted(L))]
 logs=Counter();reps={}
 for z in product(AX,repeat=4):
  it=iter(z)
  U=[(a,*(next(it)for _ in range(l-1)),b)for a,b,l in L]
  if any(len(set(p))!=len(p)for p in U):continue
  E=[edge(K[i],K[i+1])for K in U for i in range(len(K)-1)]
  if len(set(E))!=10:continue
  E=set(E);logs['distinct']+=1
  F=P-E
  if any(set(combinations(Y,2))<=F and set(combinations(sorted(set(AX)-set(Y)),2))<=F for Y in combinations(AX,4)):
   logs['K4K3']+=1
   continue
  can=min(gx(U,g)for g in group)
  reps[can]=tuple(sorted(Counter(i for p in U for i in p[1:-1]).values()))
 logs['group']=len(group)
 logs['orbits']=len(reps)
 return sorted(reps)

from functools import lru_cache
from itertools import combinations_with_replacement
E=tuple(sorted(P))
PP=tuple(combinations(range(3),2))
MS=tuple(combinations_with_replacement(range(3),2))
A=(1,0,0);B=(0,1,0);C1=(0,0,1)
def minus(d):return tuple(-x for x in d)
def plus(*a):return tuple(map(sum,zip(*a)))
def times(a,b):return sum(x*y for x,y in zip(a,b))
def gram(a,M,b):return sum(a[i]*M[i][j]*b[j]for i in range(3)for j in range(3))
def choose(kw,U):
 D={};G={};ct=4
 M={}
 for seq in U:
  if kw=='dE' and seq[0:1]==(0,)and seq[-1:]==(1,):
   if set(seq[1:-1]) & {i for x in U if (x[0],x[-1])==(2,3) for i in x[1:-1]}:
    M[seq]=A
    break
 if kw=='dE':
  shared=next(iter(M))[1]
  for seq in U:
   key=seq[0],seq[-1]
   if key==(0,1) and seq not in M:M[seq]=B
   elif key==(2,3):M[seq]=C1 if seq[1]==shared else plus(A,B,minus(C1))
   elif key==(0,2):M[seq]=minus(plus(A,B))
   elif key==(1,3):M[seq]=plus(A,B)
 elif kw=='K':
  cmap={(0,1):A,(2,3):B,(0,2):C1,(0,3):minus(plus(A,C1)),(1,2):minus(plus(B,C1)),(1,3):plus(A,B,C1)}
  M={seq:cmap[seq[0],seq[-1]]for seq in U}
 else:
  for seq in U:
   key=seq[0],seq[-1]
   if key==(0,1):M[seq]=A if len(seq)==4 else minus(plus(A,C1))
   elif key==(2,3):M[seq]=B if len(seq)==4 else minus(plus(B,C1))
   else:M[seq]=C1
  assert len(M)==6
 for seq,vec in sorted(M.items()):
  S=[seq[0]]+list(range(ct,ct+len(seq)-2))+[seq[-1]];ct+=len(seq)-2
  for i in range(len(seq)-1):
   aa,bb=seq[i:i+2];e=edge(aa,bb)
   D[e]=vec if i%2==0 else minus(vec)
   G[e,aa]=S[i];G[e,bb]=S[i+1]
 return D,G
def possM(kw):
 if kw=='K':
  for p,t,v,w,z in product((4,6,8),repeat=5):
   u=4
   ab=(v-p-u)//2;ac=(w-t-u)//2;bc=(z+u-v-w)//2
   yield ((p,bc,ab),(bc,t,ac),(ab,ac,u))
 if kw=='dO':
  for a,b,c in product(range(-4,5),(-2,-1,0),(-2,-1,0)):
   yield ((4,a,b),(a,4,c),(b,c,4))
 if kw=='dE':
  for p,q,r,s,z in product((4,6,8),repeat=5):
   ab=(z-p-q)//2;bc=(z+r-s)//2
   yield ((p,ab,0),(ab,q,bc),(0,bc,r))
def shape(m):
 return ((0,0,0,0),)if m==0 else ((0,0,1,1),)if m==1 else ((1,1,1,1),(0,1,1,2))
def direct(U,kw):
 D,G=choose(kw,U)
 unit=[2] if kw=='K' else[0,1]if kw=='dO'else[]
 def bound(e,d,de):
  if e==d:return de-2,de-2
  ss=set(e)&set(d)
  if not ss:return -1,3
  a,=ss
  if e not in D or G[e,a]!=G[d,a]:return 0,0
  return 0,2
 def mat(e,de):
  L=[(M,lo,hi)for d,M in D.items()for lo,hi in [bound(e,d,de)]]
  return tuple(v for v in product(*[(range(-1,2)if j in unit else range(-2,3)if kw!='dO'or j!=2 else range(-1,3))for j in range(3)])
             if all(lo<=times(v,M)<=hi for M,lo,hi in L))
 choices={(e,d):mat(e,d)for e in E for d in range(3)}
 mom=lambda v:tuple(v[i]*v[j]for i,j in MS)
 @lru_cache(maxsize=None)
 def opt(e,degree,T):
  L=[choices[e,j]for j in degree];S={}
  for a,b in product(*L[:2]):
   c=plus(a,b);S.setdefault(c,set()).add(plus(mom(a),mom(b)))
  return {plus(mom(a),mom(b),v)for a,b in product(*L[2:])for v in S.get(tuple(T[i]-a[i]-b[i]for i in range(3)),())}
 def feasible(choices,T):
  mn=[[0]*6];mx=[[0]*6]
  L=list(sorted(choices,key=len))
  for u in L[::-1]:
   mn.append([min(x[i]for x in u)+mn[-1][i]for i in range(6)])
   mx.append([max(x[i]for x in u)+mx[-1][i]for i in range(6)])
  @lru_cache(maxsize=None)
  def f(i,R):
   n=len(L)-i
   if any(x<mn[n][j]or x>mx[n][j]for j,x in enumerate(R)):return False
   if not n:return True
   return any(f(i+1,tuple(x-y for x,y in zip(R,u)))for u in L[i])
  return f(0,T)
 logs=Counter();passM=[]
 for M in possM(kw):
  (p,h,g),(_,q,f),(_,_,r)=M
  if any(M[i][j]**2>M[i][i]*M[j][j]for i,j in PP):continue
  if p*q*r+2*f*g*h-p*f*f-q*g*g-r*h*h<0:continue
  norm={e:gram(v,M,v)for e,v in D.items()}
  if any(n not in (4,6,8) for n in norm.values()):continue
  bad=False
  for e,d in combinations(D,2):
   u=gram(D[e],M,D[d]);S=set(e)&set(d)
   if S:
    a,=S
    if u>0 or (u!=0 and G[e,a]!=G[d,a]):bad=True;break
   elif u>4:bad=True;break
  if bad:continue
  logs['gram']+=1
  out=[]
  for e in E:
   if e in D:
    k=4-norm[e]//2;v=D[e];T=tuple(-sum(M[i][j]*v[j]for j in range(3))for i in range(3))
    S=set.union(*(opt(e,X,T)for X in shape(k)))
   else:
    S=opt(e,(2,2,2,2),(0,0,0))
   if not S:break
   out.append(S)
  else:
   logs['row']+=1
   if feasible(out,tuple(7*M[i][j]for i,j in MS)):
    logs['moment']+=1
    passM.append(M)
 return logs,passM

expected={
 'K': [(1,1,0),(1,1,0),(3,3,0),(14,14,0),(31,31,5)],
 'dO':[(1,1,1),(3,3,0),(3,3,0),(9,9,4)],
 'dE':[(29,29,3),(81,81,18)]
}
for k,L in base.items():
 orbits=main(L)
 assert len(orbits)==len(expected[k])
 for i,U in enumerate(orbits):
  log,S=direct(U,k)
  count=tuple(log[x] for x in ('gram','row','moment'))
  assert count==expected[k][i],(k,i,count)
  print(k,i,U,count,S,flush=True)
