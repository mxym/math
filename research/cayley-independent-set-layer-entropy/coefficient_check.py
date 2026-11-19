"""Second exact calculation, by all connected supports of size <=6."""
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb, factorial
from functools import lru_cache
D=6
def trees(n):
 if n==1:
  yield (0,)
  return
 for word in product(range(n),repeat=n-2):
  deg=[1]*n; adj=[0]*n
  for x in word:deg[x]+=1
  for x in word:
   u=deg.index(1); adj[x]|=1<<u; adj[u]|=1<<x;deg[u]-=1;deg[x]-=1
  v,w=[i for i in range(n) if deg[i]==1]; adj[v]|=1<<w; adj[w]|=1<<v
  yield tuple(adj)
@lru_cache(None)
def logbycoeff(z):
 f=[Q(0)]*(D+1); z=list(z)+[0]*(D+1-len(z))
 # F'=Z'/Z
 for j in range(1,D+1):
  f[j]=Q(j*z[j]-sum(i*f[i]*z[j-i] for i in range(1,j)),j)
 return f
def verify():
 sol=[Q(0)]*(D+1)
 for n in range(1,D+1):
  subtotal=[Q(0)]*(D+1)
  for t in trees(n):
   ind=[not any(B>>i&1 and t[i]&B for i in range(n)) for B in range(1<<n)]
   for A in range(1<<n):
    z=[0]*(n+1);B=A
    while True:
     if ind[B]:z[B.bit_count()]+=1
     if not B:break
     B=(B-1)&A
    f=logbycoeff(tuple(z));s=(-1)**(n-A.bit_count())
    for j in range(1,D+1):
     subtotal[j]+=s*f[j]
  for j in range(1,D+1):
   sol[j]+=Q(n,factorial(n))*subtotal[j]
 ann=[Q(0)]+[sum(Q((-j)**r,factorial(r))*(-1)**(j-1-r)*comb(j+1+j-1-r,j-1-r) for r in range(j))/j**2 for j in range(1,D+1)]
 gap=[x-y for x,y in zip(ann[1:],sol[1:])]
 if gap!=[Q(0)]*5+[Q(1,4)]:raise ArithmeticError(gap)
 print('all labeled connected tree supports by orders 1..6:',[1,1,3,16,125,1296])
 print('quenched pressure coefficients:',*[str(x) for x in sol[1:]])
 print('annealed via Lagrange inversion:',*[str(x) for x in ann[1:]])
 print('gap:',*[str(x) for x in gap])
if __name__=='__main__':verify()
