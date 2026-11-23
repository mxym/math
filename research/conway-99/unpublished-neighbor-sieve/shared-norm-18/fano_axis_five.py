"""Fano axis: a rank-independent five-family forcing inequality.
Place beside higher_moments.py and rank36_three_types.py.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
from math import isqrt
from fractions import Fraction as F
from sympy import Matrix
from higher_moments import projections, rows, GRAM, times, dot, SHIFTS
from site_degree_ten import possible, harmonic
projections=lru_cache(None)(projections)

def plus(*terms):
 r=Counter()
 for scale,d in terms:
  for k,v in d.items():r[k]+=scale*v
 return Counter({k:v for k,v in r.items() if v})
def E(a,t,k):return {(a,t,k):1}
def angular(a,t,fn=lambda k:1):
 r=Counter()
 for k in range(isqrt((2*(9*t-11*a*a))//63)+1):
  j=k%2;h=t-7*((k*k-j)//2)
  if not possible(a,h) or ((a,h) in [(0,0),(0,14)] and j):continue
  r[a,h,j]+=fn(0) if k==0 else fn(k)+fn(-k)
 return r
def coefficient_rows():
 sh=[None,*SHIFTS];out=[]
 for si,u in enumerate(sh):
  for h in [(0,0,0,0),(1,0,0,0),(0,1,0,0),(1,1,1,0),(1,2,3,1),(1,-1,1,-2)]:
   for d in [2,4,6,8,10]:
    mom=[]
    for n in [1,2,3]:
     terms=[]
     for (a,t),ws in projections(u,n).items():
      S=9*(2+dot(h,times(GRAM,h)))*2*n
      cnt=Counter((3 if u is None else 1)*dot(h,w) for w in ws)
      row=angular(a,t,lambda k:sum(v*harmonic(d,3*k+j,S) for j,v in cnt.items()))
      terms.append((1+int(a!=0),row))
     mom.append(plus(*terms))
    if d==2:
     out.append(((si,h,d,2),plus((1,mom[1]),(48,mom[0]))))
     out.append(((si,h,d,3),plus((1,mom[2]),(195804,mom[0]))))
    else:
     v,w={4:(151740,192),6:(-99180,-552),8:(50220,432),10:(-22140,-312)}[d]
     out.append(((si,h,d,3),plus((1,mom[2]),(-v,mom[0]),(-w,mom[1]))))
 chs=(((1,25),(0,16),8),((1,27),(0,18),9),((1,27),(2,26),2),((0,26),(1,21),8))
 for j,r in enumerate(rows()):
  d=dict(r)
  for target,src,m in chs:d[src]=d.get(src,0)-m*r.get(target,0)
  out.append((('old',j),plus(*[(w,angular(*k)) for k,w in d.items()])))
 return out

def target():
 # All five are automatically unit at their displayed costs.
 lhs=plus(*[(v,angular(*q)) for v,q in [(14,(0,20)),(2,(0,24)),(4,(2,26)),(4,(2,30)),(2,(3,37))]])
 lhs=plus((1,lhs),(-8,E(0,16,1)),(48,E(0,18,1)))
 a=[(4,(0,16,0)),(36,(0,20,1)),(16,(0,22,1)),(12,(0,24,1)),(1,(0,28,1)),
    (4,(1,21,1)),(72,(2,26,1)),(4,(2,28,0)),(4,(2,34,1)),(2,(3,35,0)),
    (4,(3,35,1)),(4,(3,37,1)),(2,(4,44,0)),(4,(4,44,1)),(2,(4,46,1))]
 # Expanded constant 12: 12+2(K123,1-14)+28(1-K222,1).
 rhs=plus((12,E(0,0,0)),(2,angular(1,21)),(2,E(1,23,1)),(-28,E(2,22,1)),*[(v,E(*q)) for v,q in a])
 return plus((1,lhs),(-1,rhs))
def check():
 rs=coefficient_rows();t=target();keys=sorted(set(t).union(*(set(d) for _,d in rs)))
 def vec(d):return [d.get(k,0) for k in keys]
 B=Matrix([vec(d) for k,d in rs]);q=Matrix([vec(t)])
 r=len(B.to_DM().rref()[1]);s=len(B.col_join(q).to_DM().rref()[1])
 print('raw rows, angular atoms, ranks before/after:',B.rows,B.cols,r,s)
 assert r==s==84 and len(keys)==118
if __name__=='__main__':check()
