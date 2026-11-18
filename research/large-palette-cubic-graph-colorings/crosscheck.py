"""Second finite calculation. Add one vertex at a time; canonical BFS label. For small graphs use indistinguishable independent color classes to recover the chromatic polynomial. Counts subgraphs by injections, not edge-subset enumeration."""
import itertools,sys
from functools import lru_cache
from fractions import Fraction as Q
from collections import Counter
K=int(sys.argv[1]) if len(sys.argv)>1 else 8
V=K+1

def canon(a):
 n=len(a)
 if n>=3 and all(x.bit_count()==2 for x in a):return (n,-1),2*n
 d=[x.bit_count() for x in a]
 rootdeg=min(set(d),key=lambda k:(d.count(k),k))
 best=None;m=0
 def step(seq,seen,i):
  nonlocal best,m
  if len(seq)==n:
   v=0
   for i,u in enumerate(seq):
    for j in seq[:i]:v=(v<<1)|((a[u]>>j)&1)
   if best is None or v<best:best=v;m=1
   elif v==best:m+=1
   return
  assert i<len(seq)
  new=a[seq[i]]&~seen
  for perm in itertools.permutations([j for j in range(n) if new>>j&1]):
   step(seq+perm,seen|new,i+1)
 for i in range(n):
  if d[i]==rootdeg:step((i,),1<<i,0)
 return (n,best),m
def bits(a):return [i for i in range(a.bit_length()) if (a>>i)&1]
def bicon(a):
 n=len(a)
 if n<3:return False
 for v in range(n):
  avail=((1<<n)-1)^(1<<v);comp=avail&-avail
  while True:
   extra=0
   for j in bits(comp):extra|=a[j]
   new=(extra&avail)|comp
   if new==comp:break
   comp=new
  if comp!=avail:return False
 return True
def gen(bad):
 old={None:((0,),1)};allf={}
 for n in range(1,V):
  new={}
  for a,_ in old.values():
   low=[i for i,x in enumerate(a) if x.bit_count()<3]
   for s in range(1,4):
    for att in itertools.combinations(low,s):
     if any((bool(a[i]>>j&1) if bad==3 else bool(a[i]&a[j])) for i,j in itertools.combinations(att,2)):continue
     v=1<<n;c=tuple(t+v if i in att else t for i,t in enumerate(a))+(sum(1<<i for i in att),)
     key,aut=canon(c);new[key]=(c,aut)
  old=new;allf.update({key:(a,aut) for key,(a,aut) in new.items() if bicon(a)})
 return allf
def cycle(k):return tuple((1<<((i+1)%k))+(1<<((i-1)%k)) for i in range(k))
def copies(f,g):
 n=len(f);h=len(g)
 if n>h:return 0
 seq=[];dd=[a.bit_count() for a in f]
 while len(seq)!=n:
  seq.append(max((i for i in range(n) if i not in seq),key=lambda i:(sum(f[i]>>j&1 for j in seq),dd[i])))
 def go(used,imgs):
  z=len(imgs)
  if z==n:return 1
  i=seq[z]; options=((1<<h)-1)^used
  for j,jm in zip(seq,imgs):
   if f[i]>>j&1:options&=g[jm]
  return sum(go(used+(1<<v),imgs+[v]) for v in bits(options) if g[v].bit_count()>=dd[i])
 return go(0,[])
def chrom(a):
 n=len(a); ct=[0]*(n+1)
 def coloring(i,S):
  if i==n:ct[len(S)]+=1;return
  for j,c in enumerate(S):
   if not (a[i]&c):coloring(i+1,S[:j]+[c+(1<<i)]+S[j+1:])
  coloring(i+1,S+[1<<i])
 coloring(0,[])
 d=[0]*(n+1);s=[1]
 for k,m in enumerate(ct):
  for j,q in enumerate(s):d[j]+=m*q
  s=[(s[j-1] if j else 0)-(k*s[j] if j<len(s) else 0) for j in range(len(s)+1)]
 return d[::-1]
def pwr(p):
 # Newton roots: t_k = - (k a_k + sum_{i<k} a_i t_{k-i})
 p=p+[0]*(K+1); T=[0]
 for k in range(1,K+1):T.append(-k*p[k]-sum(p[i]*T[k-i] for i in range(1,k)))
 return T
def base(kind):
 if kind=='P':
  pairs=list(itertools.combinations(range(5),2))
  return tuple(sum(1<<j for j,v in enumerate(pairs) if not set(v)&set(u)) for u in pairs)
 points=range(1,8); trip=sorted(set(tuple(sorted((u,v,u^v))) for u,v in itertools.combinations(points,2)))
 return tuple(sum(1<<(7+j) for j,t in enumerate(trip) if u in t) for u in points)+tuple(sum(1<<(u-1) for u in t) for t in trip)
def tree_lim(a):
 # A spanning tree with most leaves has a smallest connected dominating set of internal vertices (n>=3).
 n=len(a);full=(1<<n)-1
 for s in range(1,n):
  for S in itertools.combinations(range(n),s):
   mask=sum(1<<j for j in S);comp=1<<S[0];nb=0
   for i in S:nb|=a[i]
   if nb|mask!=full:continue
   while True:
    new=0
    for j in bits(comp):new|=a[j]
    new=(new&mask)|comp
    if new==comp:break
    comp=new
   if comp==mask:return 3*2**s
 raise AssertionError()
for kind in 'PH':
 g=5 if kind=='P' else 6;s=(-1)**g;X=[4] if g==5 else [3,5]; bad=3 if g==5 else 4
 A=gen(bad);processed=[]
 lb=[Q(0)]*(K+1);ledger={l:[Q(0)]*(K+1) for l in X};H=base(kind)
 for key,(a,aut) in sorted(A.items(),key=lambda item:sum(x.bit_count() for x in item[1][0])):
  n=len(a);m=sum(x.bit_count() for x in a)//2
  assert copies(a,a)==aut
  P=pwr(chrom(a)); w=[Q(0)]+[Q(m-P[k],k) for k in range(1,K+1)]
  for h,ha,old in processed:
   if n<len(h):continue
   b=copies(h,a)//ha
   if b:w=[v-b*y for v,y in zip(w,old)]
  assert list(w[:n])==[0]*(n-1)+[(-1)**m]
  processed.append((a,aut,w))
  l=next((l for l in X if copies(cycle(l),a)),None)
  if l:
   if n==m==l:
    for j,z in enumerate(w):ledger[l][j]-=s*z
   else:
    lim=Q(2*l*2**(n-l),aut)
    for j,z in enumerate(w):ledger[l][j]-=max(0,s*z)*lim
  elif n==m==g:
   assert all(s*x>=0 for x in w)
   lb[g-1]+=Q(1,g)
   if g==5:ledger[4][4]-=2
  else:
   b=Q(copies(a,H),len(H)*aut); cap=Q(tree_lim(a),aut)
   for j,z in enumerate(w):lb[j]+=s*z*b-max(0,s*z)*cap
 print('kind',kind,'size',len(A),'K',K,'const',' '.join(str(x) for x in lb),'ledger',{j:[str(x) for x in l] for j,l in ledger.items()},flush=True)
