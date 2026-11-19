"""Exact checks of the one/two-ball labeled Cayley extension formula and size bias."""
from collections import Counter,deque
from itertools import product
from math import factorial,prod,perm
from fractions import Fraction as F
def decode(seq):
 n=len(seq)+2;deg=[1]*n
 for x in seq:deg[x]+=1
 g=[[] for _ in deg]
 for x in seq:
  u=next(i for i,d in enumerate(deg) if d==1)
  g[x].append(u);g[u].append(x);deg[u]=0;deg[x]-=1
 a,b=(i for i,d in enumerate(deg) if d==1);g[a].append(b);g[b].append(a)
 return g
def ball(g,i,h):
 seen=set()
 def rec(x,p,h):
  seen.add(x)
  if h==0:return ()
  return tuple(sorted(rec(y,x,h-1) for y in g[x] if y!=p))
 return rec(i,-1,h),seen
def stats(s,h):
 c=Counter(s);t=1;b=int(h==0);a=prod(factorial(v) for v in c.values())
 for z in s:
  v,j,k=stats(z,h-1);t+=v;b+=j;a*=k
 return t,b,a
def test(n):
 C=Counter()
 for seq in product(range(n),repeat=n-2):
  g=decode(seq);entries=[[ball(g,i,h) for h in range(3)] for i in (0,1)]
  for h in range(3):
   s,A=entries[0][h];C[((h,s),)]+=1
   for k in range(3):
    q,B=entries[1][k]
    if A.isdisjoint(B):C[((h,s),(k,q))]+=1
 checks=0
 for key,count in C.items():
  ts,bs,ass=zip(*(stats(s,h) for h,s in key));T=sum(ts);U=T-sum(bs);l=len(ts)
  if T==n or min(bs)==0:continue
  guess=F(perm(n-l,T-l)*prod(bs),prod(ass))*F(n-U)**(n-T+l-2)
  if guess!=count:raise ValueError((n,key,guess,count))
  checks+=1
 return checks
if __name__=='__main__':
 for n in range(2,8): print(n,test(n))
