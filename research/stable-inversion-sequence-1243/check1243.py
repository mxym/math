from itertools import combinations,permutations
from math import comb
from functools import lru_cache
# Formula (1): explicit two-subset construction and knapsack; no search over 1243.
def coefficients(K):
 out=[0]*(K+1); bases=0
 for m in range(2,2*K+4):
  if comb(m//2,2)+comb((m+1)//2,2)>K:break
  for r in range(1,m):
   for pos in combinations(range(m),r):
    ip=set(pos)
    for vals in combinations(range(1,m+1),r):
     x=iter(vals[::-1]); y=iter(sorted(set(range(1,m+1))-set(vals),reverse=True))
     u=[next(x) if i in ip else next(y) for i in range(m)]
     if any((min(u[:i],default=m+1)<v)!=(i in ip) for i,v in enumerate(u)):continue
     e=sum(v>w for i,v in enumerate(u) for w in u[i+1:])
     if e>K:continue
     bases+=1; a=[(i,min(u[j] for j in pos if j<i)) for i in range(pos[0]+1,m)]
     s=min(vals)
     def rec(l,g,acc):
      if l==len(a):
       v=[0]*(K+1);v[g]=1
       for j in range(s,m):
        cost=m-j+sum(x for x,(_,t) in zip(acc,a) if j<t)
        for weight in range(g,K-cost+1):v[weight+cost]+=v[weight]
       for i,x in enumerate(v):out[i]+=x
       return
      di=m-a[l][0]
      for x in range((K-g)//di+1):rec(l+1,g+x*di,acc+(x,))
     rec(0,e,())
 return out,bases

# Independent direct increment: generate by insertion of a new maximum. The only new
# 1243 uses that maximum in role 4, so the prefix must not have an ascent ending
# below any suffix value. Full pattern check of individual small sizes is separate.
def direct(K):
 N=K+2; h=[[0]*(K+1) for _ in range(N+1)]; h[0][0]=1
 def rec(u,k):
  l=len(u);h[l][k]+=1 if l else 0
  if l==N:return
  suf=[0]*(l+1)
  for i in range(l-1,-1,-1):suf[i]=max(suf[i+1],u[i])
  lo=l+1; sec=l+1
  for i in range(l+1):
   if k+l-i<=K and sec>=suf[i]:
    rec(u[:i]+(l+1,)+u[i:],k+l-i)
   if i<l:
    if lo<u[i]:sec=min(sec,u[i])
    lo=min(lo,u[i])
 rec((),0)
 return h

def main():
 K=12; q,b=coefficients(17); print('coefficients 0..17:',q); print('retained boundaries:',b)
 h=direct(K)
 if q[:K+1]!=h[-1]:raise ValueError((q,h[-1]))
 # If the last nontrivial direct-sum component has two components before it,
 # those two supply 12 before its 21. Therefore after trimming the terminal
 # fixed suffix, length <= k+2 by inv >= length-number_of_components.
 for k in range(K+1):
  if any(h[n][k]!=q[k] for n in range(k+2,len(h))):raise ValueError(('stable',k))
 for n in range(8):
  hn=[0]*(K+1); ijkl=tuple(combinations(range(n),4))
  for p in permutations(range(n)):
   k=sum(p[i]>p[j] for i,j in combinations(range(n),2))
   if k<=K and not any(p[a]<p[b]<p[d]<p[c] for a,b,c,d in ijkl):hn[k]+=1
  if hn!=h[n]:raise ValueError(('literal',n))
 print('direct maximum insertion through size',K+2,'and literal quadruples through size 7: PASS')
if __name__=='__main__':main()
